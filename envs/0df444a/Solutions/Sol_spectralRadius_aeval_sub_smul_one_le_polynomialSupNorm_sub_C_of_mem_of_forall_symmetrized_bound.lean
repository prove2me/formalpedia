-- Prove2me | solution 1 for spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:41.973927+00:00
-- url     : https://prove2.me/submissions/c2beb1af-7bfc-4e4d-8bbf-bd1b518e549a

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectralRadius ℂ
        (Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ≤
      ((polynomialSupNorm (p - Polynomial.C b) K).toNNReal : ENNReal) := by
  have hm : 0 ≤ polynomialSupNorm (p - Polynomial.C b) K :=
    polynomialSupNorm_nonneg _ _
  have hshift : spectrum ℂ
      (Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) =
      spectrum ℂ (Polynomial.aeval A p) - ({b} : Set ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq]
  refine iSup₂_le fun w hw => ?_
  rw [hshift] at hw
  obtain ⟨z, hz, b', hb', rfl⟩ := hw
  rw [Set.mem_singleton_iff] at hb'
  subst b'
  have hzball :=
    spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
      A c hA hK hc hsymm p b hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hzball
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.coe_toNNReal _ hm]
  exact hzball
