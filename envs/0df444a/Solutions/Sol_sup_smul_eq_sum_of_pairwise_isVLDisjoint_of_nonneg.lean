-- Prove2me | solution 1 for sup_smul_eq_sum_of_pairwise_isVLDisjoint_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:45.409974+00:00
-- url     : https://prove2.me/submissions/c416796f-e48e-4fc9-9b5e-432a50fdec92

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg
public import Theorems.Thm_IsVLDisjoint_smul_left
public import Theorems.Thm_IsVLDisjoint_smul_right

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution {n : ℕ}
    {x : Fin n → X} {α : Fin n → ℝ} (hne : 0 < n)
    (hnn : ∀ i, 0 ≤ x i) (hα : ∀ i, 0 ≤ α i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, α i • x i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) (fun i => α i • x i) := by
  refine sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg hne
    (fun i => smul_nonneg (hα i) (hnn i)) ?_
  intro i j hij
  exact ((hdisj hij).smul_left (α i)).smul_right (α j)
