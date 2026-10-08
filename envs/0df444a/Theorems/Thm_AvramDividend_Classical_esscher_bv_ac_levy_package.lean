-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bv_ac_levy_package
-- name    : AvramDividend.Classical.esscher_bv_ac_levy_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:50:44.834058+00:00
-- url     : https://prove2.me/theorems/3ab9db75-7ac8-4619-bd87-ca83395743d0
-- title:
--   Esscher-weighted spectrally negative absolutely continuous Lévy measure package
-- statement:
--   For any spectrally negative Lévy jump measure with an absolutely continuous density and finite Lévy truncation integral, a nonnegative Esscher tilt preserves all three properties: no nonnegative jumps, absolute continuity with respect to Lebesgue measure, and finite truncated quadratic Lévy integral. This packages already independently Proved deterministic results required to define the shifted Lévy triplet of the BV/AC excursion regularity branch.
-- source:
--   Proved AvramDividend.Classical.esscher_weighted_levy_measure_support_ac and esscher_negative_jumps_levy_integrable.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_bv_ac_levy_package
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hneg : ν (Ici 0) = 0) (hac : ν ≪ volume)
    (hlevy : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) ≪ volume ∧
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ := by sorry
