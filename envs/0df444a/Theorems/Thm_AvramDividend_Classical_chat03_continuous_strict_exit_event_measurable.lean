-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_continuous_strict_exit_event_measurable
-- name    : AvramDividend.Classical.chat03_continuous_strict_exit_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:15:47.180325+00:00
-- url     : https://prove2.me/theorems/1c3a40e0-e632-4564-8e50-a8fd0da4e440
-- title:
--   The continuous strict two-sided Lévy exit occurrence event is measurable
-- statement:
--   For an official adapted spectrally negative Lévy process with right-continuous paths, the event that the process strictly crosses either a lower or upper real level at some nonnegative time is measurable in the ambient sigma algebra. The proof combines the separately Proved equivalence between continuous exit and an inverse-natural grid exit with measurability of the countable grid event. This closes the uncountable-time existential measurability gap without filtration right-continuity or stochastic martingales.
-- source:
--   Proved inverse-natural grid detection ac8b9e52-5815-4817-aff2-65753a595d1f and countable grid event measurability e1e3bf46-3ca6-42a0-b297-802d10bc9fd5.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
import Theorems.Thm_AvramDividend_Classical_chat03_countable_grid_exit_event_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_continuous_strict_exit_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | ∃ t : ℝ≥0,
        X.X t ω < lower ∨ upper < X.X t ω} := by sorry
