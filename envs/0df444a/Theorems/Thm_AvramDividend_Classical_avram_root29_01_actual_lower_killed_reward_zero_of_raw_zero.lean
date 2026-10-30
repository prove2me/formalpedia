-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero
-- name    : AvramDividend.Classical.avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:35:17.010884+00:00
-- url     : https://prove2.me/theorems/b299c1fe-21e4-4e81-a5f2-7bf5c697c5f7
-- title:
--   True lower-history-killed Lévy grid q-scale vanishes when unrestricted reward does
-- statement:
--   For the genuine original Lévy reserve path on a sequence of sampled first-exit times, if the un-killed discounted q-scale payoff is nonnegative and tends to zero, then the payoff killed by the full continuous lower-survival history also tends to zero. The lower-first branch requires no eventual identification of a negative excursion by a particular mesh: pointwise the killed payoff is sandwiched between zero and the unrestricted reward. This is the precise missing lower-first pathwise limit conversion for genuine killed-grid optional stopping.
-- source:
--   WS1A work/avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero_draft.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (x : ℝ)
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hWnonneg : ∀ n, 0 ≤ W (x + X.X (t n) ω))
    (hRawZero : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds 0) := by sorry
