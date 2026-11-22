-- Prove2me | solution 1 for sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:57.410798+00:00
-- url     : https://prove2.me/submissions/15a9b2fc-74ce-4b4f-a862-18723afc8d09

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_add_eq_sup_of_isVLDisjoint_of_nonneg
public import Theorems.Thm_isVLDisjoint_finset_sum
section
@[expose] public section
open scoped Topology
open Filter Finset
section LatticeOrdered
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
private lemma sum_eq_sup'_aux {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → X)
    (hnn : ∀ i ∈ s, 0 ≤ f i)
    (hdisj : (s : Set ι).Pairwise fun i j => IsVLDisjoint (f i) (f j)) :
    ∑ i ∈ s, f i = s.sup' hs f := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.sum_cons, Finset.sup'_cons hs f]
    have mem_cons_of : ∀ i ∈ s, i ∈ Finset.cons a s ha :=
      fun i hi => Finset.mem_cons.mpr (Or.inr hi)
    have hnn_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => hnn i (mem_cons_of i hi)
    have hnn_a : 0 ≤ f a := hnn a (Finset.mem_cons.mpr (Or.inl rfl))
    have hdisj_s : (s : Set ι).Pairwise fun i j => IsVLDisjoint (f i) (f j) := by
      intro i hi j hj hij
      exact hdisj (mem_cons_of i hi) (mem_cons_of j hj) hij
    rw [← ih hnn_s hdisj_s]
    have hsum_nn : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hnn_s
    have hdisj_sum : IsVLDisjoint (f a) (∑ i ∈ s, f i) := by
      apply isVLDisjoint_finset_sum
      intro i hi
      have hne_ai : a ≠ i := fun h => ha (h ▸ hi)
      exact hdisj (Finset.mem_cons.mpr (Or.inl rfl)) (mem_cons_of i hi) hne_ai
    exact add_eq_sup_of_isVLDisjoint_of_nonneg hnn_a hsum_nn hdisj_sum
end LatticeOrdered
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end VectorLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {n : ℕ} {f : Fin n → X}
    (hne : 0 < n) (hnn : ∀ i, 0 ≤ f i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (f i) (f j)) :
    ∑ i, f i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) f := by
  apply sum_eq_sup'_aux
  · intro i _; exact hnn i
  · intro i _ j _ hij; exact hdisj hij
