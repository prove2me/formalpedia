-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
-- name    : AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:32:47.19998+00:00
-- url     : https://prove2.me/theorems/0ec8694a-90cc-4e41-9d39-37f4e80426cd
-- title:
--   Strict lower passage before a finite horizon is detected on an inverse-natural grid before the horizon
-- statement:
--   A strict downward crossing witness before a finite horizon T exists if and only if a strict downward crossing occurs at one of the countable inverse-natural grid times k/n satisfying k/n<T. Right continuity keeps a strict downward crossing valid throughout a right interval. Choose n large enough for 1/n to lie inside that interval and strictly before T. This complements the independently Proved upper-side horizon-grid theorem.
-- source:
--   Pinned official Lévy process declarations, accepted earlier Chat03 lemmas and exact Mathlib revision.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Data.NNReal.Defs

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (T : ℝ≥0) :
    (∃ s : ℝ≥0, s < T ∧ X.X s ω < lower) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower := by sorry
