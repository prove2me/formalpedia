-- Prove2me | solution 1 for normalized_circleIntegral_resolvent_eq_one_of_normOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:20.865436+00:00
-- url     : https://prove2.me/submissions/5f09a373-f29c-47be-93d1-def8bc00bfd9

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
section
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
private theorem resolvent_eq_tsum_inv_pow_smul_pow (A : B) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    resolvent A z = ∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    have hz' : ‖A‖ < 0 := by simpa only [norm_zero] using hz
    exact (not_lt_of_ge (norm_nonneg A)) hz'
  let zu : ℂˣ := Units.mk0 z hz0
  have hscale : z • resolvent A z = resolvent (z⁻¹ • A) (1 : ℂ) := by
    simpa [zu, Units.smul_def] using
      (spectrum.units_smul_resolvent_self (r := zu) (a := A))
  have hsmall : ‖z⁻¹ • A‖ < 1 := by
    rw [norm_smul, norm_inv]
    rw [inv_mul_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz
  have hseries : resolvent (z⁻¹ • A) (1 : ℂ) = ∑' n : ℕ, (z⁻¹ • A) ^ n := by
    unfold resolvent
    rw [Algebra.algebraMap_eq_smul_one, one_smul]
    exact NormedRing.inverse_one_sub _ hsmall
  calc
    resolvent A z = z⁻¹ • (z • resolvent A z) := by
      rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
    _ = z⁻¹ • resolvent (z⁻¹ • A) (1 : ℂ) := congrArg _ hscale
    _ = z⁻¹ • ∑' n : ℕ, (z⁻¹ • A) ^ n := congrArg _ hseries
    _ = ∑' n : ℕ, z⁻¹ • (z⁻¹ • A) ^ n := (tsum_const_smul'' _).symm
    _ = ∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n := by
      congr 1
      funext n
      rw [smul_pow, smul_smul]
      congr 1
      ring
variable [NormOneClass B]
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
    (A : B) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R = (1 : B) := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hderiv : Continuous (deriv (circleMap 0 R)) :=
    (contDiff_circleMap 0 R).continuous_deriv (n := 2) (by norm_num)
  have hcircle_ne : ∀ t, circleMap 0 R t ≠ 0 := fun _ =>
    circleMap_ne_center hRpos.ne'
  have hinv : Continuous (fun t => (circleMap 0 R t)⁻¹) :=
    Continuous.inv₀ (continuous_circleMap 0 R) hcircle_ne
  let term : ℕ → C(ℝ, B) := fun n =>
    ⟨fun t => deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n), by
      exact hderiv.smul ((hinv.pow (n + 1)).smul continuous_const)⟩
  have hratio : ‖A‖ / R < 1 := (div_lt_one hRpos).mpr hR
  have hterm_norm (n : ℕ) :
      ‖(term n).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ ≤
        (‖A‖ / R) ^ n := by
    apply (ContinuousMap.norm_le _
      (pow_nonneg (div_nonneg (norm_nonneg A) hRpos.le) n)).2
    intro t
    change ‖deriv (circleMap 0 R) t •
        ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n)‖ ≤ (‖A‖ / R) ^ n
    rw [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hRpos,
      norm_I, mul_one, norm_smul, norm_pow, norm_inv, norm_circleMap_zero,
      abs_of_pos hRpos]
    calc
      R * (R⁻¹ ^ (n + 1) * ‖A ^ n‖) ≤
          R * (R⁻¹ ^ (n + 1) * ‖A‖ ^ n) := by
        gcongr
        exact norm_pow_le A n
      _ = (‖A‖ / R) ^ n := by
        rw [pow_succ]
        calc
          R * (R⁻¹ ^ n * R⁻¹ * ‖A‖ ^ n) =
              (R * R⁻¹) * (R⁻¹ ^ n * ‖A‖ ^ n) := by ring
          _ = R⁻¹ ^ n * ‖A‖ ^ n := by rw [mul_inv_cancel₀ hRpos.ne', one_mul]
          _ = (‖A‖ * R⁻¹) ^ n := by rw [mul_pow]; ring
          _ = (‖A‖ / R) ^ n := by rw [div_eq_mul_inv]
  have hsum : Summable fun n =>
      ‖(term n).restrict (⟨Set.uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖ := by
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_norm
      (summable_geometric_of_lt_one (div_nonneg (norm_nonneg A) hRpos.le) hratio)
  have hinterchange := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  have hpoint (t : ℝ) :
      (∑' n : ℕ, term n t) =
        deriv (circleMap 0 R) t • resolvent A (circleMap 0 R t) := by
    have hzt : ‖A‖ < ‖circleMap 0 R t‖ := by
      simpa only [norm_circleMap_zero, abs_of_pos hRpos] using hR
    rw [show (∑' n : ℕ, term n t) =
        ∑' n : ℕ, deriv (circleMap 0 R) t •
          ((circleMap 0 R t)⁻¹ ^ (n + 1) • A ^ n) by rfl]
    rw [tsum_const_smul'']
    congr 1
    exact (resolvent_eq_tsum_inv_pow_smul_pow A hzt).symm
  have hcircle : circleIntegral (resolvent A) 0 R =
      ∑' n : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term n t := by
    unfold circleIntegral
    rw [hinterchange]
    apply intervalIntegral.integral_congr
    intro t _
    exact (hpoint t).symm
  have hterm_as_circle (n : ℕ) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term n t) =
        circleIntegral (fun z : ℂ => z⁻¹ ^ (n + 1) • A ^ n) 0 R := by
    rfl
  have hterm_zero :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term 0 t) =
        (2 * (Real.pi : ℂ) * I) • (1 : B) := by
    rw [hterm_as_circle]
    simp only [zero_add, pow_one, pow_zero]
    rw [circleIntegral.integral_smul_const]
    rw [show circleIntegral (fun z : ℂ => z⁻¹) 0 R = 2 * (Real.pi : ℂ) * I by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hRpos.ne']
  have hterm_vanish (n : ℕ) (hn : n ≠ 0) :
      (∫ t in (0 : ℝ)..(2 * Real.pi), term n t) = 0 := by
    rw [hterm_as_circle, circleIntegral.integral_smul_const]
    have hne : (Int.negSucc n) ≠ -1 := by omega
    rw [show circleIntegral (fun z : ℂ => z⁻¹ ^ (n + 1)) 0 R = 0 by
      simpa only [sub_zero, zpow_negSucc, inv_pow] using
        (circleIntegral.integral_sub_zpow_of_ne hne 0 0 R)]
    exact zero_smul _ _
  have hsum_integrals :
      (∑' n : ℕ, ∫ t in (0 : ℝ)..(2 * Real.pi), term n t) =
        (2 * (Real.pi : ℂ) * I) • (1 : B) := by
    rw [tsum_eq_single 0]
    · exact hterm_zero
    · intro n hn
      exact hterm_vanish n hn
  rw [hcircle, hsum_integrals, smul_smul]
  have hscalar : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      I_ne_zero
  rw [inv_mul_cancel₀ hscalar, one_smul]
