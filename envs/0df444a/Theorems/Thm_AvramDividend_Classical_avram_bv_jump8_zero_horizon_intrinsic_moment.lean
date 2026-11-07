-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_zero_horizon_intrinsic_moment
-- name    : AvramDividend.Classical.avram_bv_jump8_zero_horizon_intrinsic_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:11:29.210743+00:00
-- url     : https://prove2.me/theorems/7de84153-a012-4a08-a9c2-4acef291d40d
-- title:
--   Original intrinsic marked-jump transform has no time-zero atom
-- statement:
--   The intrinsic original marked jump kernel is identically zero on the empty physical window (0,0], so its exponential is one P-almost surely, for every finite negative cutoff. This records the zero-origin convention separately from the unit-interval and semigroup stochastic obligations.
-- source:
--   At every marked point, 0 < t and t ≤ 0 is impossible; the lintegral is zero. Use X.isProbability to integrate the resulting constant-one exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_zero_horizon_intrinsic_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (k : ℕ), (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (0 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) = 1 := by sorry
