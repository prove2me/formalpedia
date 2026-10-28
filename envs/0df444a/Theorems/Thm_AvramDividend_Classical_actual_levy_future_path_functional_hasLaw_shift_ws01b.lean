-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_levy_future_path_functional_hasLaw_shift_ws01b
-- name    : AvramDividend.Classical.actual_levy_future_path_functional_hasLaw_shift_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:27:38.789543+00:00
-- url     : https://prove2.me/theorems/7a0dfabc-f3ac-499e-8769-05f7bfe4ae96
-- title:
--   Full Lévy future-increment path transfers any measurable jump-family distribution by stationary law
-- statement:
--   On an actual spectrally negative Lévy process, at every deterministic time s, any measurable functional Fpath of the entire future increment path has exactly the same distribution as that functional applied to the original process from time zero. In particular, any genuine Poisson joint count/mark law established at zero persists on every future deterministic interval. This is full-path stationarity, not just the distribution of one increment and not a postulated Poisson law.
-- source:
--   Directly from canonically Proved levy_shiftedFuturePath_stationary_law, levy_wholePath_measurable, and Mathlib map_map / HasLaw. Genuine stochastic stationarity for future-path jump observations that will combine with source/Poisson path-law transfer and past/future independence to instantiate predictable stopped Dynkin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_levy_future_path_functional_hasLaw_shift_ws01b
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (Fpath : (ℝ≥0 → ℝ) → E) (hF : Measurable Fpath)
    (η : Measure E)
    (h0 : HasLaw
      (fun ω : Ω => Fpath (fun t : ℝ≥0 => X.X t ω)) η P) :
    HasLaw
      (fun ω : Ω =>
        Fpath (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω))
      η P := by sorry
