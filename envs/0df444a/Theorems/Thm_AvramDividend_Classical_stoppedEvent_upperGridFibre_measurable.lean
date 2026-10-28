-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
-- name    : AvramDividend.Classical.stoppedEvent_upperGridFibre_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:09:02.320886+00:00
-- url     : https://prove2.me/theorems/ddc5c663-4003-4dfd-aaf7-c2d390b54283
-- title:
--   Stopped-history events are measurable on each upper-rounded finite-grid stopping fibre
-- statement:
--   If an event A is measurable in the stopped history of a finite-valued stopping time τ and τn is an adapted approximation from above with measurable time fibres, then every intersection A∩{τn=s} is measurable in the filtration at s. This discharges the past-measurability hypothesis needed to apply deterministic-time Lévy independence on each approximating grid cell.
-- source:
--   Direct ingredient for strong Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380. Applies with the finite adapted grids from Proved bounded_stopping_dyadic_grid_approximation 68cdb033-cbf7-4640-a303-5d06c3c7a761. No W or scale-function assumptions.

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stoppedEvent_upperGridFibre_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      (A ∩ {ω : Ω | τn n ω = s}) := by
  sorry
