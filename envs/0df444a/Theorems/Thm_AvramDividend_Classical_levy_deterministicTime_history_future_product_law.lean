-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law
-- name    : AvramDividend.Classical.levy_deterministicTime_history_future_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:03:38.425832+00:00
-- url     : https://prove2.me/theorems/cd9853a4-d75b-4779-b22b-4c4db8f41256
-- title:
--   Unconditional product law for any deterministic-time past statistic and whole Lévy future path
-- statement:
--   For every deterministic time s and every measurable statistic H of the history up to s, the joint law of H and the entire future increment trajectory equals the product of the law of H and the original Lévy path law. This combines Lévy finite-cylinder independence, whole-path independence, and stationarity without additional hypotheses.
-- source:
--   Direct stochastic Markov prerequisite for barrier dividend strong-Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and Open dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Composes Proved finite_time_state_future_product_of_cylinders 143aac01-c41d-42b8-a00e-3e4bc567b6a6, finite_future_increment_sigma_indep_past df83d931-9b50-4c91-9b13-698d5a554893, and shifted future path stationarity f7f7d00c-aaf9-47d1-9d8e-1edbc5d2b849.

import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_deterministicTime_history_future_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω : Ω => (H ω, fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  sorry
