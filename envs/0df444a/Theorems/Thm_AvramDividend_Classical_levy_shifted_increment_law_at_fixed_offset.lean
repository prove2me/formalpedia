-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shifted_increment_law_at_fixed_offset
-- name    : AvramDividend.Classical.levy_shifted_increment_law_at_fixed_offset
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:56:11.413761+00:00
-- url     : https://prove2.me/theorems/b0132d43-a9fa-489d-9f61-a77daceaf2ab
-- title:
--   Stationarity of a fixed future Lévy increment distribution
-- statement:
--   For each deterministic start s and future offset t, the law of the future increment X_(s+t)-X_s is exactly the law of X_t. This is the one-coordinate marginal input to finite-dimensional and ultimately whole-path shift stationarity for the strong-Markov dividend splitting proof.
-- source:
--   Direct corollary of SpectrallyNegativeLevy.stationaryIncrements. A requisite first step for full path-space distribution equality in strong Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shifted_increment_law_at_fixed_offset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) :
    Measure.map (fun ω : Ω => X.X (s + t) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => X.X t ω) P := by
  sorry
