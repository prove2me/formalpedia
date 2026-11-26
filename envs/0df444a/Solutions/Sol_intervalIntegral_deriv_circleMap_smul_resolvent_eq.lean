-- Prove2me | solution 1 for intervalIntegral_deriv_circleMap_smul_resolvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:44.135478+00:00
-- url     : https://prove2.me/submissions/804ac1f3-aac2-4e9d-8f00-8cd6705649cc

import Definitions.Def_Operator_Crouzeix_CircleKernel
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleProduct
import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_normalized_circleIntegral_resolvent_eq_one
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {R : ℝ}
    (hR : ‖A‖ < R) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv (circleMap 0 R) t • resolvent A (circleMap 0 R t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E) := by
  have h := normalized_circleIntegral_resolvent_eq_one A hR
  have h2πi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  rw [inv_smul_eq_iff₀ h2πi] at h
  exact h
