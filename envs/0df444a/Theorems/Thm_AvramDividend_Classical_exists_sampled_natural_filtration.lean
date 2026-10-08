-- Prove2me | Theorems.Thm_AvramDividend_Classical_exists_sampled_natural_filtration
-- name    : AvramDividend.Classical.exists_sampled_natural_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:39:32.802552+00:00
-- url     : https://prove2.me/theorems/2a2d3d62-fb1c-4f0e-a810-13b382192cb7
-- title:
--   Every nonnegative-time filtration restricts to a natural-time filtration
-- statement:
--   Given any filtration indexed by nonnegative real time, define a discrete filtration whose σ-algebra at step n is the original σ-algebra at time n. The filtration monotonicity and ambient measurability conditions follow from the original filtration, because the map n↦(n:ℝ≥0) preserves order.
-- source:
--   Definition of Mathlib MeasureTheory.Filtration and monotonicity of natural-to-nonnegative-real casts. This eliminates a construction assumption in the sampling lemmas used with finite-grid optional stopping in the Avram Dividend verification proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.exists_sampled_natural_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    ∃ 𝓖 : Filtration ℕ mΩ, ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0) := by sorry
