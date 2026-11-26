-- Prove2me | solution 1 for normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:46.485633+00:00
-- url     : https://prove2.me/submissions/33e8217b-88b2-4dc3-a315-8ef16e8fe1ce

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_resolvent_eq_one_of_normOne
import Theorems.Thm_contourIntegrable_circleMap_iff
import Theorems.Thm_contourIntegral_circleMap
import Theorems.Thm_contourIntegral_const_mul

section
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
private theorem smul_resolvent_eq_one_add_mul (A : B) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) :
    z • resolvent A z = 1 + A * resolvent A z := by
  have hmul : (z • (1 : B) - A) * resolvent A z = 1 := by
    have hunit : z • (1 : B) - A = (hz.unit : B) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hz.unit_spec.symm
    calc
      (z • (1 : B) - A) * resolvent A z =
          (hz.unit : B) * (↑((hz.unit)⁻¹) : B) := by
            rw [hunit, spectrum.resolvent_eq hz]
      _ = 1 := Units.mul_inv _
  rw [sub_mul, smul_mul_assoc, one_mul] at hmul
  exact eq_add_of_sub_eq hmul
variable [CompleteSpace B]
omit [CompleteSpace B] in
private theorem circleIntegrable_zpow_smul_one {R : ℝ} (n : ℕ) :
    CircleIntegrable (fun z : ℂ => z ^ n • (1 : B)) 0 R := by
  exact ((continuous_pow n).smul continuous_const).continuousOn.circleIntegrable'
private theorem circleIntegral_zpow_smul_one_eq_zero {R : ℝ} (n : ℕ) :
    circleIntegral (fun z : ℂ => z ^ n • (1 : B)) 0 R = 0 := by
  rw [circleIntegral.integral_smul_const]
  have hne : (n : ℤ) ≠ -1 := by omega
  rw [show circleIntegral (fun z : ℂ => z ^ n) 0 R = 0 by
    simpa only [sub_zero, zpow_natCast] using
      (circleIntegral.integral_sub_zpow_of_ne hne 0 0 R)]
  exact zero_smul _ _
variable [NormOneClass B]
private theorem continuousOn_resolvent_circle (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    ContinuousOn (fun z : ℂ => resolvent A z) (Metric.sphere (0 : ℂ) R) := by
  intro z hz
  have hzNorm : ‖z‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact (spectrum.hasDerivAt_resolvent_const_left
    (spectrum.mem_resolventSet_of_norm_lt (hzNorm ▸ hR))).continuousAt.continuousWithinAt
private theorem circleIntegrable_zpow_smul_resolvent (A : B) {R : ℝ}
    (hR : ‖A‖ < R) (n : ℕ) :
    CircleIntegrable (fun z : ℂ => z ^ n • resolvent A z) 0 R := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_pos hRpos]
  exact (continuous_pow n).continuousOn.smul (continuousOn_resolvent_circle A hR)
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
    (A : B) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_smul] using
        normalized_circleIntegral_resolvent_eq_one_of_normOne A hR
  | succ n ih =>
      have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
      have hsplit : circleIntegral (fun z : ℂ => z ^ (n + 1) • resolvent A z) 0 R =
          circleIntegral (fun z : ℂ => z ^ n • (1 : B) +
            A * (z ^ n • resolvent A z)) 0 R := by
        apply circleIntegral.integral_congr hRpos.le
        intro z hz
        have hzNorm : ‖z‖ = R := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hz
        have hzRes : z ∈ resolventSet ℂ A :=
          spectrum.mem_resolventSet_of_norm_lt (hzNorm ▸ hR)
        calc
          z ^ (n + 1) • resolvent A z = z ^ n • (z • resolvent A z) := by
            rw [pow_succ, smul_smul]
          _ = z ^ n • (1 + A * resolvent A z) :=
            congrArg _ (smul_resolvent_eq_one_add_mul A hzRes)
          _ = z ^ n • (1 : B) + A * (z ^ n • resolvent A z) := by
            rw [smul_add, mul_smul_comm]
      have hAint : CircleIntegrable (fun z : ℂ => A * (z ^ n • resolvent A z)) 0 R := by
        apply ContinuousOn.circleIntegrable'
        rw [abs_of_pos hRpos]
        exact continuousOn_const.mul
          ((continuous_pow n).continuousOn.smul (continuousOn_resolvent_circle A hR))
      rw [hsplit, circleIntegral.integral_add (circleIntegrable_zpow_smul_one n) hAint,
        circleIntegral_zpow_smul_one_eq_zero, zero_add]
      rw [show circleIntegral (fun z : ℂ => A * (z ^ n • resolvent A z)) 0 R =
          A * circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R by
        simpa only [contourIntegral_circleMap] using
          contourIntegral_const_mul A
            (show ContourIntegrable (fun z : ℂ => z ^ n • resolvent A z) (circleMap 0 R) by
              exact (contourIntegrable_circleMap_iff R).mpr
                (circleIntegrable_zpow_smul_resolvent A hR n))]
      rw [← mul_smul_comm, ih, pow_succ']
