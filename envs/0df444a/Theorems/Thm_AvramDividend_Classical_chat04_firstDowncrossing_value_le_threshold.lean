-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold
-- name    : AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:53:24.503661+00:00
-- url     : https://prove2.me/theorems/a041b575-e1c0-4395-8a40-dd56ba828378
-- title:
--   At a finite strict downward first passage, the right-continuous Lévy reserve is at or below the lower barrier
-- statement:
--   For a published spectrally negative Lévy process with right-continuous sample paths, if a finite time u equals the infimum of all t with X_t below any real barrier b, then X_u is at or below b. This remains valid when the process creeps down continuously and hits exactly b. It is the downward complement to the previously proved firstUpcrossing_threshold_le_value and is needed to identify the lower-boundary payoff in the stopped-scale identity.
-- source:
--   Adapted right-continuity and infimum argument from the authoritative ACCEPTED proof of AvramDividend.Classical.firstUpcrossing_threshold_le_value (UUID a5a18b2e-1a6b-45cb-9da9-054a962d5a38). The proof is self-contained for the downward event and retains the closed lower boundary needed when downward creeping occurs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞))) :
    X.X u ω ≤ b := by sorry
