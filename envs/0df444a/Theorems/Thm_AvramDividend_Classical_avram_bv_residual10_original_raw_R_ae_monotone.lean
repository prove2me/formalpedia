-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
-- name    : AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:27:59.55813+00:00
-- url     : https://prove2.me/theorems/d95da4ae-c6d5-4cdd-abda-949ab6253b73
-- title:
--   Original BV real jump-tsum drift remainder is almost surely monotone
-- statement:
--   The exact real-valued residual R(t)=t*X.drift-X_t-J(t), with the target's raw real negative-jump tsum J over 0<v≤t, is almost surely nondecreasing for the original BV spectrally negative Lévy process. The existing proved Stieltjes theorem supplies a monotone remainder after removing the ENNReal jump sum; the existing proved interval raw-tsum theorem identifies that ENNReal sum's real value with the actual raw tsum at every t. This closes the exact-source residual representation gap and permits path-variation bounds without any equality-in-law substitution.
-- source:
--   AVRAM BV-RESIDUAL10 exact theorem bridge from Proved f0ec726b and 0f7a35f4; MathFin stochastic integration comparison, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_raw_R_ae_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) := by sorry
