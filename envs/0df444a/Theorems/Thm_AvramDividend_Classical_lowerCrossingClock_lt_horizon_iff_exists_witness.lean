-- Prove2me | Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
-- name    : AvramDividend.Classical.lowerCrossingClock_lt_horizon_iff_exists_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:58:23.585825+00:00
-- url     : https://prove2.me/theorems/07415c4f-541a-41c1-9aa5-41b562447fbf
-- title:
--   Strict lower-crossing infimum precedes finite horizon iff a downward witness exists
-- statement:
--   For any Lévy sample path and lower threshold, the infimum over downward-crossing times lies strictly before a finite horizon exactly when some time before the horizon crosses below that threshold. This identifies the lower exit clock in the stopped-history killing condition of the strong-Markov barrier value theorem.
-- source:
--   Standalone order-theoretic first-passage witness identity for dividendValue_barrierStrategy_upExit_split_of_standing 79978d61-9d1f-4b20-b8a5-114797a8e380. Built with pinned Mathlib iInf_lt_iff and ENNReal order embeddings, no W assumptions.

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.lowerCrossingClock_lt_horizon_iff_exists_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ)
    (ω : Ω) (u : ℝ≥0) :
    (⨅ (s : ℝ≥0) (_ : X.X s ω < lower), (s : ℝ≥0∞)) <
      (u : ℝ≥0∞) ↔
    ∃ s : ℝ≥0, s < u ∧ X.X s ω < lower := by
  sorry
