import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.IsPrimePow
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Logic.Lemmas
set_option maxHeartbeats 5000000

theorem list_whose_finset_is_singleton {α : Type} [DecidableEq α] (lst : List α) (x : α)
    (h : lst.toFinset ⊆ {x}) : lst = List.replicate lst.length x := by
  match lst with
  | [] => simp
  | y::ys =>
    have h₁ : y = x := by
      have : y ∈ (y::ys).toFinset := by
        rw [List.mem_toFinset]; simp
      have : y ∈ {x} := by exact h this
      simp at this
      exact this
    have h₂ : ys.toFinset ⊆ {x} := by
      simp at h
      rw [← h]
      exact Finset.subset_insert y ys.toFinset
    have ih : ys = List.replicate ys.length x := list_whose_finset_is_singleton ys x h₂
    rw [h₁, ih]
    simp

theorem pow_p_increasing (p : ℕ) (h1 : Nat.Prime p): {x y: ℕ} →
  x ≤ y → ((⟨λ t => p^t, Nat.pow_right_injective h1.two_le⟩: ℕ ↪ ℕ) x) ≤
    ((⟨λ t => p^t, Nat.pow_right_injective h1.two_le⟩: ℕ ↪ ℕ) y) := by
  simp
  have h : (p > 1) := by exact Nat.Prime.one_lt h1
  intro x y h₂
  exact (pow_le_pow_iff_right h).mpr h₂

theorem list_map_toFinset {α : Type u_1} {β : Type u_2} {f : α ↪ β} [DecidableEq α] [DecidableEq β] {s : List α} :
  Finset.map f (List.toFinset s) = List.toFinset (List.map (↑f) s) := by
  match s with
  | [] => simp
  | y::ys =>
    simp
    rw [list_map_toFinset]

theorem sort_monotone_map {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
 (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
  (s : β → β → Prop) [DecidableRel s] [IsTrans β s] [IsAntisymm β s] [IsTotal β s]
    (f : α ↪ β) (preserve_lt : {x : α} → {y : α} → (h : r x y) → (s (f x) (f y)))
    (fst : Finset α): Finset.sort s (Finset.map f fst) = List.map f (Finset.sort r fst) := by
  let lst := Finset.sort r fst
  have lst_sorted : List.Sorted r lst := Finset.sort_sorted r fst
  have RHS_sorted : List.Sorted s (List.map f lst) := by
    apply List.pairwise_map.mpr
    unfold List.Sorted at lst_sorted
    exact List.Pairwise.imp preserve_lt lst_sorted
  have LHS_nodup : List.Nodup (Finset.sort s (Finset.map f fst)) := Finset.sort_nodup s (Finset.map f fst)
  have RHS_nodup : List.Nodup (List.map f (Finset.sort r fst)) := by
    apply List.Nodup.map
    exact Function.Embedding.injective f
    exact Finset.sort_nodup r fst
  have h₂ : (Finset.sort s (Finset.map f fst)).toFinset = (List.map f (Finset.sort r fst)).toFinset := by
    simp
    rw [← list_map_toFinset]
    simp
  have LHS_sorted : List.Sorted s (Finset.sort s (Finset.map f fst)) :=  Finset.sort_sorted s (Finset.map f fst)

  rw [List.toFinset_eq_iff_perm_dedup] at h₂
  rw [List.Nodup.dedup] at h₂
  rw [List.Nodup.dedup] at h₂
  exact List.eq_of_perm_of_sorted h₂ LHS_sorted RHS_sorted
  tauto
  tauto

theorem aux_eq_of_perm_of_sorted {α : Type u_1} (r : α → α → Prop) [DecidableEq α]
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
    (s t : List α) (h : List.Perm s t) (hs : List.Sorted r s) (ht : List.Sorted r t) : s = t := by
  apply List.eq_of_perm_of_sorted h hs ht

theorem list_pairwise_join_iff {α : Type*} {r : α → α → Prop} {l1 l2 : List α}:
    (l1++l2).Pairwise r ↔ (l1.Pairwise r) ∧ (l2.Pairwise r) ∧ (∀ {x y : α} (_ : x ∈ l1) (_: y ∈ l2), (r x y)) := by
  match l1 with
  | [] => simp
  | x :: xs =>
    simp [List.Pairwise]
    let h := @list_pairwise_join_iff α r xs l2
    simp_rw [h]
    --pure tautology from here
    apply Iff.intro
    intro ⟨h1,h2,h3,h4⟩
    apply And.intro
    apply And.intro
    exact (λ {u : α} (h : u ∈ xs) => h1 u (Or.inl h))
    exact h2
    apply And.intro
    exact h3
    intro u v
    intro h5
    cases h5 with
    | inl h5a => rw [h5a];exact (λ (h : v ∈ l2) => h1 v (Or.inr h))
    | inr h5b => exact (λ (h : v ∈ l2) => h4 h5b h)
    intro ⟨⟨g1,g2⟩,g3,g4⟩
    apply And.intro
    intro u
    intro g5
    cases g5 with
    | inl g6a => exact g1 u g6a;
    | inr g6b => exact g4 (Or.inl (refl x)) g6b
    apply And.intro
    exact g2
    apply And.intro
    exact g3
    exact (λ {u v : α} (h : u ∈ xs)(g : v ∈ l2) => g4 (Or.inr h) g)

theorem pairwise_tail_iff {α : Type*} {r : α → α → Prop} {a : α} {l : List α} :
    List.Sorted r (l ++ [a]) ↔ (∀ b ∈ l, r b a) ∧ List.Sorted r l := by
  unfold List.Sorted
  rw [list_pairwise_join_iff]
  --tautology + a ∈ [a] from here on
  apply Iff.intro
  intro ⟨h1,_,h3⟩
  apply And.intro
  intro u h4
  exact h3 h4 (List.mem_singleton.mpr (refl _))
  exact h1
  intro ⟨g1,g2⟩
  apply And.intro
  exact g2
  apply And.intro
  simp [List.Pairwise]
  intro u v g3 g4
  rw [List.mem_singleton] at g4
  rw [g4]
  exact g1 u g3

theorem Finset.sort_insert {α : Type u_1} (r : α → α → Prop) [DecidableEq α]
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r] (s : Finset α)
    (x : α) (h : ∀ y ∈ s, r y x) (hx : x ∉ s) :
    Finset.sort (r) (insert x s) = Finset.sort r s ++ [x] := by
  rw [←Finset.cons_eq_insert]
  swap; exact hx
  apply aux_eq_of_perm_of_sorted r
  swap
  exact sort_sorted _ _
  swap
  rw [pairwise_tail_iff]
  constructor
  · intro b hb
    simp at hb
    apply h _ hb
  exact sort_sorted _ _
  apply (Finset.sort_perm_toList _ _).trans
  apply (Finset.toList_cons hx).trans
  apply List.Perm.trans _ (List.perm_append_singleton _ _).symm
  rw [List.perm_cons]
  apply (Finset.sort_perm_toList _ _).symm


theorem finset_sorted_range {k : ℕ} :
    (Finset.sort (. ≤ .) (Finset.range k)) = List.range k := by
  induction k with
  | zero => simp
  | succ n ih =>
  rw [@Finset.range_succ]
  rw [List.range_succ]
  rw [← ih]
  rw [Finset.sort_insert]
  intro y
  simpa using le_of_lt
  simp

theorem list_take_mem_iff {α: Type*} (a : α) (n : ℕ) (l : List α):
    a ∈ l.take n ↔ ∃ k : Fin l.length, k.val < n ∧ l.get k = a := by
  apply Iff.intro
  intro h
  rw [List.mem_iff_get] at h
  let ⟨k,hk⟩ := h
  let hk₁ := k.isLt
  simp at hk₁
  use ⟨k,by omega⟩
  apply And.intro
  tauto
  rw [List.get_take (L:=l) (j:=n)]
  tauto
  tauto
  intro ⟨k,hk₁,hk₂⟩
  rw [List.mem_iff_get]
  use ⟨k,by simp;omega⟩
  rw [List.get_take']
  simp
  tauto

theorem list_drop_mem_iff {α: Type*} (a : α) (n : ℕ) (l : List α):
    a ∈ l.drop n ↔ ∃ k : Fin l.length, k.val ≥ n ∧ l.get k = a := by
  apply Iff.intro
  intro h
  rw [List.mem_iff_get] at h
  let ⟨k,hk⟩ := h
  let hk₁ := k.isLt
  simp at hk₁
  use ⟨n+k,by omega⟩
  apply And.intro
  simp
  rw [List.get_drop (i:=n)]
  tauto
  intro ⟨k,hk₁,hk₂⟩
  let hk₃ := k.isLt
  rw [List.mem_iff_get]
  use ⟨k.val-n,by simp;omega⟩
  rw [List.get_drop']
  simp
  have : n+(k.val-n) = k.val := by omega
  simp_rw [this]
  tauto

theorem finset_le_sort_get {α : Type*} (r : α → α → Prop) [DecidableEq α]
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
    {s : Finset α}{n : Fin (s.card)}:
    ∀ x : α, ((Finset.sort r s).get ⟨n,by rw [Finset.length_sort]; exact Fin.prop n⟩ = x)
      → (s.filter (λ y => r y x)) = (List.take (n.val + 1) (Finset.sort r s)).toFinset := by
  intro u
  intro h
  have subset1 : (s.filter (λ y => r y u)) ⊆ (List.take (n.val + 1) (Finset.sort r s)).toFinset := by
    intro x hx
    simp
    have hx₁ : x ∈ Finset.sort r s := by
      rw [Finset.mem_sort]
      exact Finset.mem_of_mem_filter x hx
    simp at hx
    let ⟨_,hx₃⟩ := hx
    let hx₄ := hx₁
    rw [← List.take_append_drop (l := Finset.sort r s) (n := n.val + 1)] at hx₄
    by_contra hxnot
    rw [List.mem_append] at hx₄
    have hxindrop : x ∈ List.drop (↑n + 1) (Finset.sort r s) := by tauto
    rw [list_drop_mem_iff x (n.val + 1) (Finset.sort r s)] at hxindrop
    let ⟨k,hk₁,hk₂⟩ := hxindrop
    let hk₃ := k.isLt
    simp at hk₃
    have hrux : r u x := by
      let a : Fin (Finset.sort r s).length := ⟨n,by simp⟩
      let b : Fin (Finset.sort r s).length := k
      rw [← h]
      rw [← hk₂]
      apply List.Sorted.rel_get_of_le (r:=r) (l:=Finset.sort r s) (a:=a) (b:=b)
      exact Finset.sort_sorted r s
      exact LT.lt.le hk₁
    have hequx : u = x := by
      apply antisymm' (r:=r)
      tauto
      tauto

    rw [← h] at hequx
    rw [← hk₂] at hequx
    rw [List.Nodup.get_inj_iff] at hequx
    let heqind := Fin.veq_of_eq hequx
    simp at heqind
    omega
    exact Finset.sort_nodup r s

  have subset2 : (List.take (n.val + 1) (Finset.sort r s)).toFinset ⊆ (s.filter (λ y => r y u)) := by
    intro y hy
    simp at hy
    simp
    apply And.intro
    have : y ∈ Finset.sort r s := by exact List.mem_of_mem_take hy
    exact (Finset.mem_sort r).mp this
    rw [list_take_mem_iff] at hy
    let ⟨k,hk₁,hk₂⟩ := hy
    rw [← hk₂]
    rw [←h]
    apply List.Sorted.rel_get_of_le
    exact Finset.sort_sorted r s
    rw [← Fin.val_fin_le]
    simp
    omega

  exact Finset.Subset.antisymm subset1 subset2

theorem list_sort_sublist {α: Type*}(r : α → α → Prop) [DecidableEq α]
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
    {l₁ l₂ : List α} : List.Sublist l₁ l₂ → List.Sorted r l₂ → List.Sorted r l₁ := by
  exact List.Pairwise.sublist

theorem finset_le_sort_get_card {α : Type*} (r : α → α → Prop) [DecidableEq α]
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
    {s : Finset α}{n : Fin (s.card)}:
    ∀ x ∈ s, ((Finset.sort r s).get ⟨n,by rw [Finset.length_sort]; exact Fin.prop n⟩ = x)
      ↔ (s.filter (λ y => r y x)).card = n.val + 1 := by
  intro x hx₀
  apply Iff.intro
  intro hx
  rw [finset_le_sort_get (r:=r) (n:=n)]
  rw [List.card_toFinset]
  rw [List.Nodup.dedup]
  simp
  let hn := n.isLt
  omega

  apply List.Nodup.sublist (l₂ := Finset.sort r s)
  exact List.take_sublist (↑n + 1) (Finset.sort r s)
  exact Finset.sort_nodup r s
  exact hx

  intro h
  have : x ∈ Finset.sort r s := (Finset.mem_sort r).mpr hx₀
  rw [List.mem_iff_get] at this
  let ⟨k,hk⟩ := this
  rw [← hk]

  congr
  exact (Finset.length_sort r).symm
  rw [Fin.heq_ext_iff]
  swap
  exact (Finset.length_sort r).symm

  rw [← hk] at h
  let hk₁ := k.isLt
  simp at hk₁
  rw [finset_le_sort_get (r:=r) (n:=⟨k,hk₁⟩)] at h
  rw [List.card_toFinset] at h
  rw [List.Nodup.dedup] at h
  simp at h
  have : k.val + 1 ≤ s.card := by omega
  simp [this] at h
  tauto

  apply List.Nodup.sublist (l₂ := Finset.sort r s)
  apply List.take_sublist (l:=Finset.sort r s)
  exact Finset.sort_nodup r s
  simp

theorem sorted_zero {α : Type*} [LinearOrder α]
    (s : Finset α) (h : 0 < ((s.sort (. ≤ .)).length)) (H : s.Nonempty) :
    (s.sort (. ≤. )).get ⟨0, by simp; rw [Finset.card_pos]; exact H⟩ = s.min' H := by
  let l := s.sort (· ≤ ·)
  apply le_antisymm
  · have : s.min' H ∈ l := (Finset.mem_sort (α := α) (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    apply (s.sort_sorted (· ≤ ·)).rel_get_of_le
    rw [← Fin.val_fin_le]
    simp
  · have : l.get ⟨0, h⟩ ∈ s := (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l 0 h)
    exact s.min'_le _ this

theorem sorted_zero_le {α : Type*} [LinearOrder α]
    (l : List α) (h : 0 < l.length) (hsorted : List.Sorted (. ≤ .) l):
    ∀ x ∈ l, l.get ⟨0, h⟩ ≤ x := by
  intro x hx
  rw [List.mem_iff_get] at hx
  let ⟨n,hn⟩ := hx
  rw [← hn]
  apply List.Sorted.rel_get_of_le
  exact hsorted
  rw [Fin.le_iff_val_le_val]
  simp

def Composite (n : ℕ) : Prop := (n > 1) ∧ ¬(Nat.Prime n)

def sorted_divisors (n : ℕ) : List ℕ := Finset.sort (. ≤ .) (Nat.divisors n)

theorem sorted_divisors_nodup (n : ℕ) : (sorted_divisors n).Nodup := by
  unfold sorted_divisors
  exact Finset.sort_nodup (fun x x_1 => x ≤ x_1) (Nat.divisors n)

theorem sorted_divisors_sorted (n : ℕ) : List.Sorted (. ≤ .) (sorted_divisors n) := by
  unfold sorted_divisors
  exact Finset.sort_sorted (fun x x_1 => x ≤ x_1) (Nat.divisors n)

theorem sorted_divisors_mem_dvd (n : ℕ) : ∀ x ∈ sorted_divisors n, x ∣ n := by
  unfold sorted_divisors
  intro x hx
  rw [Finset.mem_sort (α := ℕ) (r:= (. ≤ .))] at hx
  simp at hx
  tauto
theorem sorted_divisors_mem_neqzero (n : ℕ) : ∀ x ∈ sorted_divisors n, x ≠ 0 := by
  unfold sorted_divisors
  intro x hx
  rw [Finset.mem_sort (α := ℕ) (r:= (. ≤ .))] at hx
  simp at hx
  by_contra eqzero
  let wrong := hx.left
  rw [eqzero] at wrong
  simp at wrong
  exact hx.right wrong

theorem sorted_divisors_get_dvd (n : ℕ) (k : Fin (sorted_divisors n).length):
    (sorted_divisors n).get k ∣ n := by
  suffices :(sorted_divisors n).get k ∈ (sorted_divisors n)
  apply sorted_divisors_mem_dvd
  exact this
  rw [List.mem_iff_get]
  exact exists_apply_eq_apply (fun a => List.get (sorted_divisors n) a) k

theorem composite_numdivisors_ge_three (n : ℕ) (h : Composite n) :
    (Nat.divisors n).card ≥ 3 := by
  -- Prove that n ≠ 1, which is a necessary condition to apply Nat.exists_prime_and_dvd
  have neq_one : n ≠ 1 := ne_of_gt h.left
  unfold Composite at h

  -- n is composite, so it has a nontrivial prime divisor p
  let ⟨p,hp⟩ :=  Nat.exists_prime_and_dvd neq_one

  -- Establish that 1, p, and n are distinct divisors of n
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.one_dvd _, ne_of_gt (by omega)⟩
  have hp' : p ∈ n.divisors := Nat.mem_divisors.2 ⟨hp.2, by omega⟩
  have hn : n ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.dvd_refl _, by omega⟩

  -- Construct the subset {1, p, n} of divisors of n
  have con1 : {1, p, n} ⊆ n.divisors := by
    intro x
    intro hx
    simp at hx
    match hx with
    | Or.inl h => rw [h]; assumption
    | Or.inr (Or.inl h) => rw [h]; assumption
    | Or.inr (Or.inr h) => rw [h]; assumption

  -- The set {1, p, n} has exactly 3 elements
  have con2 : Finset.card {1, p, n} = 3 := by
    rw [Finset.card_eq_three]
    use 1, p, n
    apply And.intro
    suffices : Nat.Prime p
    exact Ne.symm (Nat.Prime.ne_one this)
    tauto
    apply And.intro
    omega
    apply And.intro
    intro hpn
    let h₄ := h.right
    rw [← hpn] at h₄
    exact h₄ hp.left
    rfl

  -- Conclude the proof
  let con3 := @Finset.card_le_card ℕ {1,p,n} n.divisors con1
  rw [con2] at con3
  tauto

theorem zeroth_divisor (n : ℕ)(hn : n ≠ 0) :
    (sorted_divisors n).get
      ⟨0, by
        apply List.length_pos_of_mem (a:=1)
        unfold sorted_divisors
        simp
        tauto
      ⟩ = 1 := by

  unfold sorted_divisors
  have : 1 ∈ Finset.sort (. ≤ .) (n.divisors) := by
    simp
    tauto
  let hminsuf := sorted_zero (s:=n.divisors) (H := by simp;tauto) (List.length_pos_of_mem this)
  rw [hminsuf]
  apply le_antisymm
  apply Finset.min'_le
  rw [Nat.one_mem_divisors]
  exact hn
  apply Finset.le_min'
  intro y hy
  unfold Nat.divisors at hy
  have : y ∈ (Finset.Ico 1 (n + 1)) := by exact Finset.mem_of_mem_filter y hy
  simp at this
  tauto

theorem first_divisor_aux (n : ℕ)(hn : n > 1):
    1< (sorted_divisors n).length := by

  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.one_dvd _, ne_of_gt (by omega)⟩
  have hn : n ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.dvd_refl _, by omega⟩

  have con1 : {1, n} ⊆ n.divisors := by
    intro x
    intro hx
    simp at hx
    match hx with
    | Or.inl h => rw [h]; assumption
    | Or.inr h => rw [h]; assumption

  have con2 : Finset.card {1, n} = 2 := by
    rw [Finset.card_eq_two]
    use 1, n
    apply And.intro
    omega
    rfl

  -- Conclude the proof
  let con3 := @Finset.card_le_card ℕ {1,n} n.divisors con1
  rw [con2] at con3
  unfold sorted_divisors
  simp
  omega

theorem first_divisor (n : ℕ)(hn : n > 1) :
    (sorted_divisors n).get ⟨1, first_divisor_aux n hn⟩ =
      Nat.minFac n := by
  let oneoftype: Fin (sorted_divisors n).length :=
    ⟨1, first_divisor_aux n hn⟩
  apply le_antisymm
  have : n.minFac ∈ sorted_divisors n := by
    suffices : n.minFac ∈ n.divisors
    unfold sorted_divisors
    exact (Finset.mem_sort (α := ℕ) fun x x_1 => x ≤ x_1).mpr this
    simp
    apply And.intro
    exact Nat.minFac_dvd n
    omega
  rw [List.mem_iff_get] at this
  let ⟨k,hk⟩ := this
  rw [← hk]
  have : k.val > 0 := by
    by_contra heqzero
    simp at heqzero
    have : k = ⟨0,by let hfst := first_divisor_aux n hn;omega⟩ := by
      apply Fin.eq_of_val_eq
      simp
      tauto
    rw [this] at hk
    rw [zeroth_divisor n (by omega)] at hk
    symm at hk
    rw [Nat.minFac_eq_one_iff (n:=n)] at hk
    omega
  apply List.Sorted.rel_get_of_le (α := ℕ) (r:= (. ≤ .))
  unfold sorted_divisors
  exact Finset.sort_sorted (fun x x_1 => x ≤ x_1) (Nat.divisors n)
  rw [Fin.le_iff_val_le_val]
  simp
  omega
  apply Nat.minFac_le_of_dvd
  suffices : (sorted_divisors n).get oneoftype ≥ 1
  by_contra h
  have : (sorted_divisors n).get oneoftype = 1 := by omega
  let hzero := zeroth_divisor n (Nat.not_eq_zero_of_lt hn)
  rw [← hzero] at this
  rw [List.Nodup.get_inj_iff] at this
  let impossible := Fin.val_eq_of_eq this
  simp at impossible
  unfold sorted_divisors
  exact Finset.sort_nodup (fun x x_1 => x ≤ x_1) (Nat.divisors n)
  suffices : ∀ x ∈ sorted_divisors n, x ≥ 1
  have hincl: (sorted_divisors n).get oneoftype ∈ sorted_divisors n := by
    exact List.get_mem (sorted_divisors n) 1 (first_divisor_aux n hn)
  exact this (List.get (sorted_divisors n) oneoftype) hincl
  intro x hx
  unfold sorted_divisors at hx
  simp at hx
  suffices : x ≠ 0
  exact Nat.one_le_iff_ne_zero.mpr this
  let ⟨hx₁,hx₂⟩ := hx
  exact ne_zero_of_dvd_ne_zero hx₂ hx₁
  suffices : ∀ x ∈ sorted_divisors n, x ∣ n
  apply this
  exact List.get_mem (sorted_divisors n) 1 (first_divisor_aux n hn)
  intro x hx
  unfold sorted_divisors at hx
  simp at hx
  tauto

theorem sorted_divisors_reverse (n : ℕ)(hn : n ≠ 0) :
    (sorted_divisors n).reverse = List.map (λ x => n/x) (sorted_divisors n) := by
  rw [List.reverse_eq_iff]
  apply List.eq_of_perm_of_sorted (α := ℕ) (r := (. ≤ .))
  apply List.perm_of_nodup_nodup_toFinset_eq
  exact sorted_divisors_nodup n
  rw [List.nodup_reverse]
  rw [List.nodup_iff_injective_get]
  unfold Function.Injective
  intro a₁ a₂ ha1a2
  let b₁ : Fin (sorted_divisors n).length := ⟨a₁.val, by
    let h := a₁.isLt
    simp at h
    tauto⟩
  let b₂ : Fin (sorted_divisors n).length := ⟨a₂.val, by
    let h := a₂.isLt
    simp at h
    tauto⟩
  suffices : (sorted_divisors n).get b₁ = (sorted_divisors n).get b₂
  rw [List.Nodup.get_inj_iff] at this
  rw [Fin.eq_iff_veq] at this
  rw [Fin.eq_iff_veq]
  tauto
  exact sorted_divisors_nodup n
  simp at ha1a2
  have h₁ : n/(n/((sorted_divisors n).get b₁)) = (sorted_divisors n).get b₁ := by
    apply Nat.div_div_self
    apply sorted_divisors_get_dvd
    exact hn
  have h₂ : n/(n/((sorted_divisors n).get b₂)) = (sorted_divisors n).get b₂ := by
    apply Nat.div_div_self
    apply sorted_divisors_get_dvd
    exact hn
  have : n/(n/((sorted_divisors n).get b₁)) = n/(n/((sorted_divisors n).get b₂)) := by
    rw [ha1a2]
  rw [h₁] at this
  rw [h₂] at this
  exact this
  apply Finset.Subset.antisymm
  intro x hx
  unfold sorted_divisors at hx
  simp at hx
  simp
  use (n/x)
  apply And.intro
  unfold sorted_divisors
  simp
  apply And.intro
  apply Nat.div_dvd_of_dvd
  exact hx.left
  exact hn
  apply Nat.div_div_self
  exact hx.left
  exact hn
  intro x hx
  simp at hx
  let ⟨a,ha₁,ha₂⟩ := hx
  unfold sorted_divisors at ha₁
  simp at ha₁
  simp
  unfold sorted_divisors
  simp
  apply And.intro
  rw [← ha₂]
  apply Nat.div_dvd_of_dvd
  exact ha₁.left
  exact hn
  exact sorted_divisors_sorted n
  unfold List.Sorted
  rw [List.pairwise_reverse]
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem (R := (. ≤ .))
  intro a b ha hb hineq
  apply Nat.div_le_div_left
  exact hineq
  unfold sorted_divisors at ha
  simp at ha
  by_contra hzero
  simp at hzero
  let wrong := ha.left
  rw [hzero] at wrong
  simp at wrong
  contradiction
  rw [← List.Sorted]
  exact sorted_divisors_sorted n

theorem list_get_eq {α : Type*}{l1 l2 : List α}
    {n : Fin l1.length}{m: Fin l2.length}(hl : l1 = l2)(hmn :m.val = n.val) :
    l1.get n = l2.get m := by
  congr
  exact (Fin.heq_ext_iff (congrArg List.length hl)).mpr (id hmn.symm)

theorem sorted_divisors_reverse_get (n : ℕ)(hn : n ≠ 0) (k : Fin (sorted_divisors n).length):
    (sorted_divisors n).get k = n/((sorted_divisors n).get ⟨(sorted_divisors n).length -1 -k.val,by have := k.isLt;omega⟩) := by
  rw [← List.get_reverse (l:= sorted_divisors n) (i:=k.val) (h1 := by simp;have:= k.isLt;omega) (h2 := k.isLt)]

  suffices :
    List.get (List.reverse (sorted_divisors n)) ⟨List.length (sorted_divisors n) - 1 - ↑k, by simp;have:= k.isLt;omega⟩ =
      List.get (List.map (λ x => n/x) (sorted_divisors n)) ⟨List.length (sorted_divisors n) - 1 - ↑k, by simp;have:= k.isLt;omega⟩
  rw [this]
  simp
  apply list_get_eq
  exact sorted_divisors_reverse n hn
  simp


def has_divisibility_property (n : ℕ) : Prop :=
  ∀ i : Fin ((sorted_divisors n).length - 2),
    let h₁ : i < ((sorted_divisors n).length- 2) := i.isLt
    let di := (sorted_divisors n).get ⟨i.val, by omega⟩
    let di1 := (sorted_divisors n).get ⟨i.val + 1, by omega⟩
    let di2 := (sorted_divisors n).get ⟨i.val + 2, by omega⟩
    di ∣ (di1 + di2)


theorem has_divisibility_property_iff (n : ℕ) :
  (∀ i : Fin ((sorted_divisors n).length - 2),
    let h₁ : i < ((sorted_divisors n).length- 2) := i.isLt
    let di := (sorted_divisors n).get ⟨i.val, by omega⟩
    let di1 := (sorted_divisors n).get ⟨i.val + 1, by omega⟩
    let di2 := (sorted_divisors n).get ⟨i.val + 2, by omega⟩
    di ∣ (di2 + di1)) ↔ has_divisibility_property n := by
  apply Iff.intro
  intro h
  intro i
  simp
  rw [Nat.add_comm]
  simp at h
  exact h i
  intro h
  intro i
  simp
  rw [Nat.add_comm]
  simp at h
  exact h i


theorem div_reverse {n m k : ℕ}(knz : k ≠ 0)(mnz : m ≠ 0)
    (hm : m ∣ n )(hk : k ∣ n )(h : (n/m) ∣ k) : (n/k) ∣ m := by
  obtain ⟨u, hu⟩ := hm -- n = m * u
  obtain ⟨v, hv⟩ := hk -- n = k * v
  obtain ⟨w, hw⟩ := h  -- k = (n/m) * w
  use w
  suffices : m * k = (n/k) * w * k
  apply Nat.eq_of_mul_eq_mul_right (m:=k)
  exact Nat.pos_of_ne_zero knz
  exact this
  suffices : (m * k = n / k * k * w)
  linarith
  rw [Nat.div_mul_cancel (n:=k) (m:=n)]
  rw [hu]
  suffices : k = u * w
  rw [this]
  ring
  suffices : n/m = u
  exact (Mathlib.Tactic.Ring.mul_congr (id this.symm) rfl (id hw.symm)).symm
  rw [hu]
  rw [Nat.mul_div_cancel_left]
  exact Nat.pos_of_ne_zero mnz
  exact Dvd.intro v (id hv.symm)


theorem div_reverse_rw {n m k : ℕ}(knz : k ≠ 0)(mnz : m ≠ 0)
    (hm : m ∣ n )(hk : k ∣ n ): (n/m) ∣ k ↔  (n/k) ∣ m := by
  apply Iff.intro
  exact fun a => div_reverse knz mnz hm hk a
  exact fun a => div_reverse mnz knz hk hm a

theorem div_prop_implies_dvd (n : ℕ)(hc : Composite n) (hprop : has_divisibility_property n):
    (sorted_divisors n).get ⟨1,by
      have := composite_numdivisors_ge_three n hc
      unfold sorted_divisors
      simp only [Finset.length_sort, gt_iff_lt]
      omega
    ⟩ ∣ (sorted_divisors n).get ⟨2,by
      have := composite_numdivisors_ge_three n hc
      unfold sorted_divisors
      simp only [Finset.length_sort, gt_iff_lt]
      omega
    ⟩ := by
  unfold has_divisibility_property at hprop
  have : (sorted_divisors n).length ≥ 3 := by
    unfold sorted_divisors
    simp only [Finset.length_sort, ge_iff_le]
    exact composite_numdivisors_ge_three n hc
  have inp := hprop ⟨(sorted_divisors n).length - 3,
    Nat.sub_succ_lt_self (List.length (sorted_divisors n)) 2 this⟩
  simp at inp
  have nneq : n ≠ 0 := by
    unfold Composite at hc
    omega
  have eq1: (sorted_divisors n).length - 3 + 1 = (sorted_divisors n).length - 2 := by omega
  simp [eq1] at inp
  have eq2: (sorted_divisors n).length - 3 + 2 = (sorted_divisors n).length - 1 := by omega
  simp [eq2] at inp
  have : List.get (sorted_divisors n) ⟨(sorted_divisors n).length - 1, by omega⟩ = n := by
    rw [sorted_divisors_reverse_get]
    simp
    rw [Nat.div_eq_self]
    apply Or.inr
    apply zeroth_divisor
    exact nneq
    exact nneq

  rw [this] at inp
  rw [Nat.dvd_add_left] at inp
  rw [sorted_divisors_reverse_get] at inp
  simp at inp
  have :(sorted_divisors n).length - 1 - ((sorted_divisors n).length - 3) = 2 := by omega
  simp [this] at inp
  rw [div_reverse_rw] at inp
  have eq3: (sorted_divisors n).length - 1 - 1 = (sorted_divisors n).length - 2 := by omega
  simp_rw [← eq3] at inp
  rw [← sorted_divisors_reverse_get (n:=n) (k:=⟨1,by
    have := composite_numdivisors_ge_three n hc
    unfold sorted_divisors
    simp only [Finset.length_sort, gt_iff_lt]
    omega
  ⟩)] at inp
  exact inp
  exact nneq
  suffices : ∀ x ∈ sorted_divisors n, x ≠ 0
  apply this
  rw [List.mem_iff_get]
  tauto
  intro x hx
  exact sorted_divisors_mem_neqzero n x hx
  apply sorted_divisors_mem_neqzero
  rw [List.mem_iff_get]
  tauto
  apply sorted_divisors_mem_dvd
  rw [List.mem_iff_get]
  tauto
  apply sorted_divisors_mem_dvd
  rw [List.mem_iff_get]
  tauto
  exact nneq
  apply sorted_divisors_mem_dvd
  rw [List.mem_iff_get]
  tauto

theorem div_prop_implies_res
  (n : ℕ) (hc : Composite n) (hprop : has_divisibility_property n) (kmax : Fin ((sorted_divisors n).length + 1)) :
  ∀ k : Fin (sorted_divisors n).length, k.val > 0 → k.val < kmax →
    (sorted_divisors n).get ⟨1, by
      have := composite_numdivisors_ge_three n hc
      unfold sorted_divisors
      simp only [Finset.length_sort, gt_iff_lt]
      omega
    ⟩ ∣ (sorted_divisors n).get k :=
by
  rcases kmax with ⟨k_val, k_is_lt⟩
  induction k_val with
  | zero => simp
  | succ l ih =>
    intro k hk₁ hk₂
    have : k.val < l ∨ k.val = l := by
      exact Nat.lt_succ_iff_lt_or_eq.mp hk₂
    cases this with
    | inl hthis =>
      apply ih (k:= k)
      exact hk₁
      exact hthis
      exact Nat.lt_of_succ_lt k_is_lt
    | inr hthis =>
      have : (l=0) ∨ (l=1) ∨ (l=2) ∨ (l > 2) := by omega
      rcases this with ha1 | ha2 | ha3 | ha4
      exfalso
      omega
      have : k = ⟨1,by
        have := composite_numdivisors_ge_three n hc
        unfold sorted_divisors
        simp only [Finset.length_sort, gt_iff_lt]
        omega
      ⟩ := by
        apply Fin.eq_of_veq
        simp_rw [ha2] at hthis
        exact hthis
      rw [this]
      have : k = ⟨2,by
        have := composite_numdivisors_ge_three n hc
        unfold sorted_divisors
        simp only [Finset.length_sort, gt_iff_lt]
        omega
      ⟩ := by
        apply Fin.eq_of_veq
        simp_rw [ha3] at hthis
        exact hthis
      rw [this]
      apply div_prop_implies_dvd
      assumption
      assumption
      rw [← Nat.add_sub_cancel (m:= (sorted_divisors n).get ⟨k.val-1,by omega⟩)
            (n:=List.get (sorted_divisors n) k)]
      apply Nat.dvd_sub' (n:= (sorted_divisors n).get ⟨k.val-1,by omega⟩)
      apply Nat.dvd_trans (b:= (sorted_divisors n).get ⟨k.val-2,by omega⟩)
      apply ih
      simp only [gt_iff_lt, tsub_pos_iff_lt]
      exact Nat.lt_of_lt_of_eq ha4 (id hthis.symm)
      simp only
      rw [hthis]
      omega
      exact Nat.lt_of_succ_lt k_is_lt
      rw [← has_divisibility_property_iff] at hprop
      simp at hprop
      let inp := hprop ⟨k.val - 2, by omega⟩
      simp at inp
      have : k.val - 2 + 2 = k.val := by omega
      simp_rw [this] at inp
      have : k.val - 2 + 1 = k.val - 1 := by omega
      simp_rw [this] at inp
      exact inp
      apply ih
      simp
      rw [hthis]
      omega
      simp
      omega
      omega

theorem div_prop_implies_ppow (n : ℕ)(hc : Composite n) (hprop : has_divisibility_property n) :
    IsPrimePow n := by
  unfold Composite at hc
  have ngt1 := hc.left
  rw [isPrimePow_iff_card_primeFactors_eq_one]
  rw [Finset.card_eq_one]
  use n.minFac
  apply subset_antisymm
  swap
  simp
  apply And.intro
  apply Nat.minFac_prime
  omega
  apply And.intro
  exact Nat.minFac_dvd n
  omega
  intro x hx
  simp at hx
  have : x ∈ sorted_divisors n := by
    unfold sorted_divisors
    simp
    apply And.intro
    tauto
    omega
  rw [List.mem_iff_get] at this
  let ⟨k,hk⟩ := this
  rw [← hk]
  simp
  have : (sorted_divisors n).length ≥ 3 := by
    let inp := composite_numdivisors_ge_three n hc
    unfold sorted_divisors
    simp
    omega
  have : k.val > 0 := by
    by_contra kzerop
    have : k = ⟨0,by omega⟩ := by
      rw [Fin.eq_iff_veq]
      exact Nat.eq_zero_of_not_pos kzerop
    let prob := hx.left
    rw [← hk] at prob
    rw [this] at prob
    rw [zeroth_divisor (n:=n)] at prob
    exact Nat.not_prime_one prob
    omega
  let pprime := hx.left
  rw [← hk] at pprime
  symm
  rw [← Nat.prime_dvd_prime_iff_eq (p:=Nat.minFac n) (q:= (sorted_divisors n).get k)]
  rw [← first_divisor]
  apply div_prop_implies_res (kmax := (sorted_divisors n).length)
  assumption
  assumption
  exact this
  have := k.isLt
  simp
  exact ngt1
  apply Nat.minFac_prime
  omega
  exact pprime


def sorted_prime_Factors (n : ℕ) : List ℕ := Finset.sort (. ≤ .) (Nat.primeFactors n)

theorem zeroth_sorted_prime_minfac_aux (n : ℕ) (hn : n > 1) :
    0 < (sorted_prime_Factors n).length := by
  unfold sorted_prime_Factors
  simp
  refine Finset.Nonempty.card_pos ?_
  rw [Nat.nonempty_primeFactors]
  exact hn

theorem sorted_prime_Factors_prime (n: ℕ) : ∀ x ∈ sorted_prime_Factors n, Nat.Prime x := by
  intro x hx
  unfold sorted_prime_Factors at hx
  simp at hx
  tauto

theorem sorted_prime_Factors_dvd (n: ℕ) : ∀ x ∈ sorted_prime_Factors n, x ∣ n  := by
  intro x hx
  unfold sorted_prime_Factors at hx
  simp at hx
  tauto

theorem zeroth_sorted_prime_minfac (n : ℕ) (hn : n > 1) :
    (sorted_prime_Factors n).get ⟨0,zeroth_sorted_prime_minfac_aux n hn⟩ = n.minFac := by
  apply le_antisymm
  have : n.minFac ∈ sorted_prime_Factors n := by
    unfold sorted_prime_Factors
    simp
    apply And.intro
    apply Nat.minFac_prime
    omega
    apply And.intro
    apply Nat.minFac_dvd
    omega
  apply sorted_zero_le
  exact Finset.sort_sorted (fun x x_1 => x ≤ x_1) n.primeFactors
  exact this
  apply Nat.minFac_le_of_dvd
  apply Nat.Prime.two_le
  apply sorted_prime_Factors_prime (n:= n)
  exact List.get_mem (sorted_prime_Factors n) 0 (zeroth_sorted_prime_minfac_aux n hn)
  apply sorted_prime_Factors_dvd (n:=n)
  exact List.get_mem (sorted_prime_Factors n) 0 (zeroth_sorted_prime_minfac_aux n hn)

theorem composite_nprimepow_implies_twoprimefac (n: ℕ)(hc : Composite n)(hnpp : ¬(IsPrimePow n)):
    n.primeFactors.card > 1 := by
  unfold Composite at hc
  rw [isPrimePow_iff_card_primeFactors_eq_one] at hnpp
  apply Ne.lt_of_le' hnpp
  apply Finset.Nonempty.card_pos
  rw [Nat.nonempty_primeFactors]
  tauto


theorem ppow_sorted_div (p k: ℕ) (hp : Nat.Prime p) :
    ∀ i : Fin (List.length (sorted_divisors (p^k))), (sorted_divisors (p^k)).get i = p^(i.val) := by
  have hdiv := Nat.divisors_prime_pow hp k
  unfold sorted_divisors
  rw [hdiv]
  let pow_p_injective := (⟨λ x => p^x, Nat.pow_right_injective (Nat.Prime.two_le hp)⟩: ℕ ↪ ℕ)
  rw [sort_monotone_map (α := ℕ) (β := ℕ) (s:= (. ≤ .)) (r := (. ≤ .)) (f := pow_p_injective)]
  rw [finset_sorted_range]
  simp
  exact fun {x y} h => pow_p_increasing p hp h


theorem prime_power_iff_special_divisor_property (n : ℕ) (hc : Composite n) :
  has_divisibility_property n ↔ IsPrimePow n := by
  apply Iff.intro
  (
    exact fun a => div_prop_implies_ppow n hc a
  )
  (
    --Showing that prime powers satisfy the property
    --First describing the prime factors of prime powers
    --should be shorter bc it uses the divisors set
    intro ⟨p,k,h₁,h₂,h₃⟩
    rw [has_divisibility_property];

    have h₄: ∀ i : Fin (List.length (sorted_divisors ↑n)),
        (sorted_divisors n).get i = p^(i.val) := by
      rw [← h₃]
      apply ppow_sorted_div
      exact Nat.prime_iff.mpr h₁
    intro i
    have := i.isLt
    rw [h₄ ⟨i.val,by omega⟩]
    rw [h₄ ⟨i.val+1,by omega⟩]
    rw [h₄ ⟨i.val+2,by omega⟩]
    simp
    apply Dvd.dvd.add
    exact Dvd.intro p rfl
    apply Dvd.intro (p^2)
    rw [pow_add]
  )
