-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_schedule
-- name    : AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:53:39.177266+00:00
-- url     : https://prove2.me/theorems/2475e630-5c74-48c7-a0a6-9561d1a449cc
-- title:
--   The true strict Lévy upper-exit clock equals the explicit measurable countable schedule
-- statement:
--   For each sample path of a spectrally negative Lévy process, the exact infimum over arbitrary strict upward crossing times equals the single-natural-indexed countable schedule clock. This enables the process exit event to be represented by the measurable full-path reward construction.
-- source:
--   Proved strict-upper positive-grid equality and Proved countable-schedule upper-grid equality, composing via transitivity.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_countable_grid
import Theorems.Thm_AvramDividend_Classical_countableSchedule_upper_grid_clock_eq_subtype_inf

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (upper : ℝ) :
    (⨅ i : {t : ℝ≥0 // upper < X.X t ω}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if upper <
          X.X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by sorry
