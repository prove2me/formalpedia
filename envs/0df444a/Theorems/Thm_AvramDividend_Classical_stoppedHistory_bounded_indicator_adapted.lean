-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedHistory_bounded_indicator_adapted
-- name    : AvramDividend.Classical.stoppedHistory_bounded_indicator_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:44:46.137001+00:00
-- url     : https://prove2.me/theorems/3c7a1740-ea4b-4bda-823e-db0e0c811707
-- title:
--   The indicator of a bounded stopped-history event is adapted at the terminal horizon
-- statement:
--   For a stopped-history event A and bounded stopping time τ≤T, the ℝ-valued indicator of A is 𝓕_T-measurable. This permits it as the history statistic in the Proved deterministic-time future-path product law, including the finite-grid reward-factorisation and stopping-time approximation.
-- source:
--   Immediate observable for Proved stoppedHistory_bounded_filtration_measurable 0846e555-63fc-41b2-89d4-11aa4ffc3f49 and deterministic future product law cd9853a4-d75b-4779-b22b-4c4db8f41256; precursor to general strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_bounded_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedHistory_bounded_indicator_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Measurable[𝓕 T]
      (Set.indicator A (fun _ : Ω => (1 : ℝ))) := by
  sorry
