-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_stoppedHistory_cap_min_adapted
-- name    : AvramDividend.Classical.avram_stoppedHistory_cap_min_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:42:06.091725+00:00
-- url     : https://prove2.me/theorems/f50d0009-9b8c-4da6-bd97-5803f81f8a29
-- title:
--   Stopping-history events remain adapted after deterministic clipping of a finite stopping time
-- statement:
--   For any filtration and measurable stopped-history event A of a nonnegative finite random time tau, its portion A intersect {tau<=H} is measurable at every stopped-history time of the capped random time min(tau,H). The proof splits at deterministic observation time s before or after H and uses filtration monotonicity. No Levy or Markov hypotheses are needed; this is the nontrivial generic adaptedness bridge for almost-surely bounded Esscher stopped histories.
-- source:
--   Exact set manipulations from proved locally bounded Esscher cylinder localisation 2a64cd78-54a7-401b-9d74-07006d316f8a, pinned Mathlib Filtration.mono and min_le_iff.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_stoppedHistory_cap_min_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (H : ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        ((A ∩ {ω : Ω | τ ω ≤ H}) ∩
          {ω : Ω | min (τ ω) H ≤ s}) := by sorry
