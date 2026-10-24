-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
-- name    : AvramDividend.Classical.levy_upper_grid_stopped_reserve_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:17:45.863253+00:00
-- url     : https://prove2.me/theorems/e5ff8b24-70d1-496e-af31-c78c46ac3318
-- title:
--   Measurability of Lévy reserve and time at a capped upper-only grid hitting index
-- statement:
--   For a spectrally negative Lévy process X and a deterministic NNReal grid clock, let K be the bounded first strict sampled upper passage index, K=hittingBtwn (X(clock k)) (Ioi z) 0 m. Assuming the sampled filtration H agrees with 𝓕(clock k), both X(clock(Kω))(ω) and the real clock(Kω) are measurable functions of ω. Apply the pinned Adapted.isStoppingTime_hittingBtwn, discrete strongly progressive stopped-value measurability and strong adaptation of a constant-in-ω clock. This is the one-sided counterpart of the already proved two-sided stopped-reserve/time lemma.

import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_upper_grid_stopped_reserve_time_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (z : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω) :
    Measurable (fun ω => X.X (clock (K ω)) ω) ∧
    Measurable (fun ω => (clock (K ω) : ℝ)) := by sorry
