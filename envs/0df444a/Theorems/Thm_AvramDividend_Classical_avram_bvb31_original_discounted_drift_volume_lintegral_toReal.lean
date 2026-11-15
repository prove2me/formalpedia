-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_discounted_drift_volume_lintegral_toReal
-- name    : AvramDividend.Classical.avram_bvb31_original_discounted_drift_volume_lintegral_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:05:31.015092+00:00
-- url     : https://prove2.me/theorems/1346e9f7-adfa-4d0e-a90d-783ff308055d
-- title:
--   Real discounted original drift-volume cash equals toReal of nonnegative Stieltjes lintegral
-- statement:
--   For a nonnegative physical drift coefficient d, positive discount q and nonnegative true horizon T, show the toReal of the original discounted nonnegative real-to-ENNReal integral against drift-scaled Lebesgue measure on (0,T] equals d times the ordinary real discounted time integral. This is the exact measure conversion needed to combine the Proved original constant-reserve Stieltjes cash theorem b9af8a7f with the Proved original closed-cap compensated time budget f2242dea. Do not discard the negative-mark compensator elsewhere.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal, lintegral_smul_measure, and Proved 5ce1f298 discounted integral identity.

import Mathlib
open Classical MeasureTheory Filter Set intervalIntegral
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb31_original_discounted_drift_volume_lintegral_toReal
    (d q T : ℝ) (hd : 0 ≤ d) (hq : 0 < q) (hT : 0 ≤ T) :
    (∫⁻ t in Ioc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂((ENNReal.ofReal d) • (volume : Measure ℝ))).toReal =
      d * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) := by sorry
