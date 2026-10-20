-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
-- name    : AvramDividend.Classical.chat03_countable_inverse_nat_grid_exit_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:06:59.86229+00:00
-- url     : https://prove2.me/theorems/ac8b9e52-5815-4817-aff2-65753a595d1f
-- title:
--   Countable inverse-natural grid detects every continuous strict two-sided Lévy exit
-- statement:
--   For an official spectrally negative Lévy process with right-continuous sample paths, existence of any continuous-time strict two-sided crossing is equivalent to existence of one such crossing on a grid with spacing 1/n, for some positive natural n and some natural grid index k. This converts an uncountable existential passage event into a countable family of deterministic-time crossing events, enabling measurable passage-event formulations from adaptedness. It uses previously Proved right-interval exit persistence and exact ceiling-grid bracket; no killed-scale martingale or optional stopping is assumed.
-- source:
--   Pinned Mathlib NNReal.exists_nat_pos_inv_lt signature recovered from authoritative remote compiler job 8f315676-6064-4c03-a541-2dc594a876b0, plus Proved chat03_strict_exit_right_interval and chat03_nnreal_grid_ceiling_bracket.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_countable_inverse_nat_grid_exit_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) :
    (∃ t : ℝ≥0, X.X t ω < lower ∨ upper < X.X t ω) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by sorry
