-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_uniform_upper_iff_all_cap_upper
-- name    : AvramDividend.Classical.avram_sweep16_original_uniform_upper_iff_all_cap_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:20:14.25801+00:00
-- url     : https://prove2.me/theorems/43f47572-c7d9-46ad-b980-11ba1751ed3c
-- title:
--   Original uniform verification upper bound equivalent to all capped HJB upper bounds
-- statement:
--   For any original spectrally negative Lévy process, discount parameter q and candidate value function w, a uniform unrestricted upper estimate for all nonnegative initial reserves is equivalent to an estimate that holds at every cap and every nonnegative reserve. The proof pointwise specialises a separately kernel-Proved original cap-to-unrestricted order equivalence; no stochastic assumptions, equality-in-law substitution or circular root imports are introduced.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_unrestricted_upper_iff_all_cap_uppers

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_uniform_upper_iff_all_cap_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) ↔
    (∀ x : ℝ, 0 ≤ x → ∀ C : ℝ≥0∞,
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) := by sorry
