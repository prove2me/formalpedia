-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_history_future_split
-- name    : AvramDividend.Classical.chat04_lower_killing_history_future_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:52:03.483405+00:00
-- url     : https://prove2.me/theorems/828dc705-b605-4f4d-8dac-36270020af43
-- title:
--   Exact one-sided historical and shifted-future killing-event factorisation
-- statement:
--   For any Levy reserve and s≤u, downward-ruin survival for the entire closed horizon [0,u] is exactly survival to s intersected with survival of the post-s shifted increment path. This follows samplewise without optional stopping or harmonicity. It supplies the correct survival event decomposition for the killed q-scale martingale.
-- source:
--   Pathwise decomposition of the historical downward-killing event required by the strict Avram two-sided exit q-scale martingale, using only order of deterministic times and Lévy increments.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_killing_history_future_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω} =
      {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω} ∩
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)} := by sorry
