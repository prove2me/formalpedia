-- Prove2me | solution 1 for normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_normOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:32.461252+00:00
-- url     : https://prove2.me/submissions/c17558d8-5ce1-4ce7-8b4e-fd9cc6ec53e7

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
section
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
private theorem continuousOn_resolvent_circle (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    ContinuousOn (fun z : ℂ => resolvent A z) (Metric.sphere (0 : ℂ) R) := by
  intro z hz
  have hzNorm : ‖z‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact (spectrum.hasDerivAt_resolvent_const_left
    (spectrum.mem_resolventSet_of_norm_lt (hzNorm ▸ hR))).continuousAt.continuousWithinAt
private theorem circleIntegrable_eval_smul_resolvent (A : B) {R : ℝ}
    (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    CircleIntegrable (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_pos hRpos]
  exact p.continuous.continuousOn.smul (continuousOn_resolvent_circle A hR)
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
theorem _root_.solution
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => Polynomial.eval z p • resolvent A z) 0 R =
        Polynomial.aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun : (fun z : ℂ => Polynomial.eval z (p + q) • resolvent A z) =
          fun z => Polynomial.eval z p • resolvent A z +
            Polynomial.eval z q • resolvent A z := by
        funext z
        rw [Polynomial.eval_add, add_smul]
      rw [hfun, circleIntegral.integral_add
        (circleIntegrable_eval_smul_resolvent A hR p)
        (circleIntegrable_eval_smul_resolvent A hR q), smul_add, hp, hq,
        Polynomial.aeval_add]
  | monomial n a =>
      have hfun : (fun z : ℂ => Polynomial.eval z (Polynomial.monomial n a) • resolvent A z) =
          fun z => a • (z ^ n • resolvent A z) := by
        funext z
        rw [Polynomial.eval_monomial, smul_smul]
      rw [hfun, circleIntegral.integral_smul, smul_smul]
      rw [show (2 * (Real.pi : ℂ) * I)⁻¹ * a =
          a * (2 * (Real.pi : ℂ) * I)⁻¹ by ring]
      rw [← smul_smul, normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne A hR n]
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
