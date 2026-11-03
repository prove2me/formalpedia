-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_increment_square_integrable
-- name    : AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:37:46.519881+00:00
-- url     : https://prove2.me/theorems/0a99afd0-6e5b-446a-a2ed-4005ece40c22
-- title:
--   Original shifted future Lévy increment centred at its source mean has integrable square
-- statement:
--   Assume the original source X_t has finite first and second absolute moments. Then at every future origin s the squared future increment, centred by its original expected value, is integrable under the original P. This gives source-specific L² integrability for centred increments; it does not assert a Poisson marked-jump isometry or a stopped truncation limit.
-- source:
--   W7-06 L² centred original future increment moment interface for martingale difference/UI development.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hFirst : Integrable (X.X t) P)
    (hSecond : Integrable (fun ω => (X.X t ω)^2) P) :
    Integrable (fun ω =>
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P))^2) P := by sorry
