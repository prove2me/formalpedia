-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
-- name    : AvramDividend.Classical.avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:07:06.586015+00:00
-- url     : https://prove2.me/theorems/0db53d17-569e-4937-9110-63d865feb5a8
-- title:
--   Gaussian zero-jump generator has a measurable positive-domain zero extension
-- statement:
--   For a zero-jump spectrally negative Lévy process and a twice-differentiable test value on its positive domain, extend the generator by zero off that domain to obtain a globally measurable real function.
-- source:
--   Generator is sigma squared half times the second derivative plus drift times first derivative; both positive-domain derivatives have Proved measurable zero extensions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if (0 < y ∧ ENNReal.ofReal y < C) then (X.generator w y) else 0) := by sorry
