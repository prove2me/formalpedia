-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strictLower_exit_subtype_inf_eq_schedule
-- name    : AvramDividend.Classical.levy_strictLower_exit_subtype_inf_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:54:30.463988+00:00
-- url     : https://prove2.me/theorems/853a27f6-65a1-447a-b34e-514db413c9aa
-- title:
--   The true strict Lévy lower-exit clock equals the explicit measurable countable schedule
-- statement:
--   For each sample path of a spectrally negative Lévy process, the exact infimum over arbitrary strict downward crossing times equals the single-natural-indexed countable schedule clock. This pairs with the strict upper schedule identity to identify the measurable two-sided exit event.
-- source:
--   Proved strict-lower positive-grid equality and lower countable schedule-grid bridge once accepted; composition via transitivity.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictLower_exit_subtype_inf_eq_countable_grid
import Theorems.Thm_AvramDividend_Classical_countableSchedule_lower_grid_clock_eq_subtype_inf

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_strictLower_exit_subtype_inf_eq_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (lower : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω < lower}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if
          X.X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω < lower
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by sorry
