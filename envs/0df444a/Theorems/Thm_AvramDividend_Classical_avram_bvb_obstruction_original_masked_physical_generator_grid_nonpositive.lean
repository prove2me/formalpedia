-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_masked_physical_generator_grid_nonpositive
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_masked_physical_generator_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:55:16.697696+00:00
-- url     : https://prove2.me/theorems/33e257db-766e-4a4b-97c8-e8d3b20e04dd
-- title:
--   Original BV strict-interior masked physical Lévy generator cell grid is nonpositive for HJB supersolution
-- statement:
--   For any original Lévy generator supersolution on 0<reserve<C and any nondecreasing physical grid, every masked discounted generator cell and their finite sum are nonpositive. The arbitrary additional predictable clock mask does not change this sign. This is the direct hG premise needed by the Proved original B=G a.e. bridge to establish hAllB in the positive-cap BV cash counterexample.
-- source:
--   On each selected interior cell, use HJB residual≤0, exp>0 and nonnegative physical cell length. Outside the clock/interior mask the term is exactly zero. Finset.sum_nonpos yields the full generator grid bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_masked_physical_generator_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1))
    (Z : ℕ → ℕ → Ω → ℝ) (clock : ℕ → ℕ → Ω → Prop)
    (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n + 1),
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
