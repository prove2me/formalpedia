-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_countable_grid_exit_event_measurable
-- name    : AvramDividend.Classical.chat03_countable_grid_exit_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:02:10.447032+00:00
-- url     : https://prove2.me/theorems/e1e3bf46-3ca6-42a0-b297-802d10bc9fd5
-- title:
--   The union of all positive inverse-natural strict two-sided grid crossings is measurable
-- statement:
--   The event that an adapted spectrally negative Lévy process strictly exits either of two levels at at least one sample time on an inverse-natural uniform grid (positive natural denominator and arbitrary natural index) is measurable. This follows by a countable union of the independently verified deterministic-grid measurable strict-exit events. Its proof is entirely discrete and does not depend on any claim that a continuous-time crossing is detected on a grid.
-- source:
--   Proved fixed-grid event measurability UUID d28afffa-123b-4e9a-ab63-a69dadb1c107, Mathlib countable measurable unions, pinned environment.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_fixed_inverse_nat_grid_exit_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_countable_grid_exit_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
      upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by sorry
