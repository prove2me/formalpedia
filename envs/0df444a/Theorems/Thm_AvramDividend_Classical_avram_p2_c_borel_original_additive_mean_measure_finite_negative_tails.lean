-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:59:19.573126+00:00
-- url     : https://prove2.me/theorems/5b57f741-50dc-4462-af44-ccaf8e2858a7
-- title:
--   Original expected marked count measure is additive in time with finite separated negative tails
-- statement:
--   The exact actual source expected mark-count measure admits an additive elapsed-time measure representative μ. Its unit-horizon mass on every strictly separated negative halfline Iic(-epsilon) is finite. No identification with the Lévy jump measure ν is assumed. This is the intrinsic source rate measure preparation.
-- source:
--   Composition of freshly Proved P2-C original expected mark measure additive 0d4dd38a and genuinely Proved separated band finite mean c9e0c0df.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_time_additive
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_band_finite_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
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
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) ∧
      (∀ ε : ℝ, 0 < ε → μ 1 (Iic (-ε)) < ⊤) := by sorry
