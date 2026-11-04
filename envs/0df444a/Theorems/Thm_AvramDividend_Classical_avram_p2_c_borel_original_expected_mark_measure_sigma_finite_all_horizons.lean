-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:55:27.462992+00:00
-- url     : https://prove2.me/theorems/1bb36998-8f59-4189-a053-f0bcfda2362b
-- title:
--   Original intrinsic expected Lévy mark measures are sigma-finite at every horizon
-- statement:
--   At each nonnegative time horizon, the exact expected original Lévy jump-mark-count measure is sigma-finite. For positive horizons, source separated-tail count finiteness gives the finite negative bands; at zero horizon, the counted interval is empty. All horizons have strict negative support. This remains independent of the prescribed Lévy ν-rate.
-- source:
--   Depends on Proved source negative support 4d799f07, Proved source band finite mean c9e0c0df and the conditional generic sigma-finiteness bridge 4092a314 once Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ T : ℝ≥0, SigmaFinite (μ T)) := by sorry
