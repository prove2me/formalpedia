-- Prove2me | solution 1 for spectrum_sub_smul_one_subset_ball_of_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:00.753309+00:00
-- url     : https://prove2.me/submissions/606ab718-02fd-4c73-8b8b-7ef5758094c3

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter

set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {r : ℝ}
    (hσ : spectrum ℂ A ⊆ Metric.ball c r) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆ Metric.ball (0 : ℂ) r := by
  have hshift : spectrum ℂ (A - c • (1 : E →L[ℂ] E)) = spectrum ℂ A - ({c} : Set ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
  rw [hshift]
  rintro w ⟨z, hz, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
  exact hσ hz
