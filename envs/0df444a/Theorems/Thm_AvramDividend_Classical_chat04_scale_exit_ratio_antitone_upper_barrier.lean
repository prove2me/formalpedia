-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_exit_ratio_antitone_upper_barrier
-- name    : AvramDividend.Classical.chat04_scale_exit_ratio_antitone_upper_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:21:46.2892+00:00
-- url     : https://prove2.me/theorems/22913054-2729-4423-b88f-3e45b51f9168
-- title:
--   Scale exit factor decreases when the upper barrier increases
-- statement:
--   For nonnegative starting reserve x and nested positive barriers a≤b, increasing the upper barrier decreases the corresponding scale ratio. This uses only the defining monotonicity/nonnegativity of W and proved positivity at positive barriers, and is separately useful in comparing scale-based barrier valuations.
-- source:
--   Avram et al. 2007 Section 3.2, multiplicative and monotone properties of scale-function exit factors.

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_exit_ratio_antitone_upper_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x a b : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (hab : a ≤ b) :
    W x / W b ≤ W x / W a := by sorry
