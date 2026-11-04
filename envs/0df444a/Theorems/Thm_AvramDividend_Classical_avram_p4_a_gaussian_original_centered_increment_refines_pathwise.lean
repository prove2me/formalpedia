-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centered_increment_refines_pathwise
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_centered_increment_refines_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:38:18.432509+00:00
-- url     : https://prove2.me/theorems/7cb14fe2-ce48-4e3b-8058-c33e11ac3b8b
-- title:
--   Original same-path jump-subtracted continuous residual increments refine exactly at random clocks
-- statement:
--   For the actual source Lévy process X, its exactly defined jump-subtracted and drift-centred path residual Z is additive across any three path-dependent clocks. This gives a source-exact deterministic grid-refinement identity for future construction of the Gaussian stochastic integral; it does not infer measurability, stopping times, martingale laws or Levy-Ito extraction.
-- source:
--   Algebraic telescoping identity applied to the original SpectrallyNegativeLevy.X trajectories and explicit source drift X.c, for arbitrary intrinsic jump sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_centered_increment_refines_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (s u t : Ω → ℝ≥0) :
    let Z : ℝ≥0 → Ω → ℝ := fun r ω =>
      X.X r ω - (r : ℝ) * X.c - Jsmall r ω - Jlarge r ω
    ∀ ω, Z (t ω) ω - Z (s ω) ω =
      (Z (u ω) ω - Z (s ω) ω) +
      (Z (t ω) ω - Z (u ω) ω) := by sorry
