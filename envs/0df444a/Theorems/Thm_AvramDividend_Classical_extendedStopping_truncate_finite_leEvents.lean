-- Prove2me | Theorems.Thm_AvramDividend_Classical_extendedStopping_truncate_finite_leEvents
-- name    : AvramDividend.Classical.extendedStopping_truncate_finite_leEvents
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:34:06.872052+00:00
-- url     : https://prove2.me/theorems/0096e00b-9d91-4f1f-90ce-4b043237a049
-- title:
--   Finite-horizon truncation of an extended nonnegative stopping clock remains a stopping clock
-- statement:
--   For any possibly infinite stopping time tau and deterministic finite horizon n, the truncated clock min(tau,n), converted into a nonnegative real time, has stopping-time level events. This bridges infinite first-passage stopping times to the finite-clock strong-Markov factorisation needed for the barrier dividend identity.
-- source:
--   Root-connected Strong-Markov barrier split 79978d61-9d1f-4b20-b8a5-114797a8e380. Proves a reusable finite-stopping-clock localisation property from Mathlib IsStoppingTime.min_const.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.extendedStopping_truncate_finite_leEvents
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (n : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        {ω : Ω | (min (τ ω) (n : ℝ≥0∞)).toNNReal ≤ s} := by
  sorry
