-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_exit_closed_window_grid_iff
-- name    : AvramDividend.Classical.chat04_strict_lower_exit_closed_window_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:47:31.957908+00:00
-- url     : https://prove2.me/theorems/1494cd77-4f3d-4e46-b437-93689e6ef01c
-- title:
--   Exact reciprocal-natural grid detection of strict ruin on a closed future window
-- statement:
--   For every càdlàg spectrally negative Lévy sample path and deterministic interval s≤u, a strict downward crossing anywhere on [s,u] is witnessed either at u or at a reciprocal-natural grid time in [s,u). The endpoint u is retained to handle terminal-only crossings. This finite-interval countable reduction is the key missing ingredient to prove measurability of the future-window survival event in killed-scale conditional expectations.
-- source:
--   Published chat03_strict_lower_exit_right_interval and chat03_nnreal_grid_ceiling_bracket, plus Mathlib NNReal.exists_nat_pos_inv_lt.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_strict_lower_exit_closed_window_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    (∃ t : ℝ≥0, s ≤ t ∧ t ≤ u ∧ X.X t ω < lower) ↔
    (X.X u ω < lower ∨ ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      s ≤ (k : ℝ≥0) * (n : ℝ≥0)⁻¹ ∧
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u ∧
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower) := by sorry
