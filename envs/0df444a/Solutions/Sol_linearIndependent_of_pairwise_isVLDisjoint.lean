-- Prove2me | solution 1 for linearIndependent_of_pairwise_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:49.919343+00:00
-- url     : https://prove2.me/submissions/83f67920-4858-4b68-9774-c59bf60c47f1

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_sum_of_pairwise_isVLDisjoint
public import Theorems.Thm_abs_eq_zero_iff_zero


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution {n : ℕ} {x : Fin n → X}
    (hne : ∀ i, x i ≠ 0)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    LinearIndependent ℝ x := by
  rw [Fintype.linearIndependent_iff]
  intro α hsum i
  have habs : |∑ i, α i • x i| = ∑ i, |α i| • |x i| :=
    abs_sum_of_pairwise_isVLDisjoint hdisj
  rw [hsum, abs_zero] at habs
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ |α j| • |x j| :=
    fun j _ => smul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hzero : |α i| • |x i| = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp habs.symm i (Finset.mem_univ i)
  by_contra hα
  have habs_ne : |α i| ≠ 0 := fun h => hα (abs_eq_zero.mp h)
  have hxi : |x i| = 0 := by
    have h2 : |α i|⁻¹ • (|α i| • |x i|) = |α i|⁻¹ • (0 : X) := by rw [hzero]
    rwa [smul_smul, inv_mul_cancel₀ habs_ne, one_smul, smul_zero] at h2
  exact hne i ((abs_eq_zero_iff_zero (x i)).mp hxi)
