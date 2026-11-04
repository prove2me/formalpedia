-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:05:16.210738+00:00
-- url     : https://prove2.me/theorems/9bbf7f85-18e1-4606-9d47-36dd5920b91d
-- title:
--   Actual source finite-horizon expected marked Lévy jump count is a genuine Borel measure on negative mark space
-- statement:
--   The first moment of the actual source intrinsic marked jump count over (0,T] defines a Borel measure on the mark coordinate. Obtain the full time-mark expected occupation measure already proved for the genuine original Lévy process and project its restriction to (0,T]×ℝ along the mark coordinate, using Measure.map/restrict. No rate identity or Poisson model appears in the statement or proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) :
    ∃ μ : Measure ℝ, ∀ B : Set ℝ, MeasurableSet B →
      μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) ∂P) := by sorry
