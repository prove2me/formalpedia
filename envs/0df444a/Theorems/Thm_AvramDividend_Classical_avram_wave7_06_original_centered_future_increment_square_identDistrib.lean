-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_increment_square_identDistrib
-- name    : AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_square_identDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:39:11.494357+00:00
-- url     : https://prove2.me/theorems/f4d2e3a2-71cd-4826-9318-8e78172bc1d2
-- title:
--   Original mean-centred future increment squares have the stationary original law
-- statement:
--   For the actual original Lévy process and an integrable source X_t, the square of the future increment centred by the original mean E[X_t] has the same distribution under original P as the square of X_t centred by that mean. This is a genuine law transfer on the same Ω and P, useful for source L² variance bounds.
-- source:
--   W7-06 original source centred future variance stationarity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_square_identDistrib
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hFirst : Integrable (X.X t) P) :
    IdentDistrib
      (fun ω => (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P))^2)
      (fun ω => (X.X t ω -
        (∫ η, X.X t η ∂P))^2)
      P P := by sorry
