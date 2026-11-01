-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_largejump_weighted_section_integrable
-- name    : AvramDividend.Classical.avram_wave4_05_source_largejump_weighted_section_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:00:54.012992+00:00
-- url     : https://prove2.me/theorems/d024c69d-f63b-4636-9c26-0850215923be
-- title:
--   Original uncompensated large-jump weighted state sections are integrable with a uniform bound
-- statement:
--   For every jump magnitude r>=1 and Laplace parameter with theta>=0 and psi(theta)>q, the actual source generatorIntegrand W x(-r) is uncompensated and its exponentially weighted absolute value is integrable on all positive states, not merely assigned a possibly vacuous Bochner integral. The x-section absolute integral is at most (psi(theta)-q)^(-1) uniformly in r. This complements the Gaussian compensated small-jump quadratic x-section bound in the source Fubini argument.
-- source:
--   Source uncompensated generatorIntegrand_large_negative 4809dc4e, scaleFunction_shiftedLaplace_integrable da4289b8, chat07_scale_uncompensated_jump_large_uniform_bound 4f069279, pinned Mathlib, mission 1300fbe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_uncompensated_jump_large_uniform_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Large jumps are uncompensated: genuine weighted state-section
    integrability, not only a potentially vacuous Bochner integral inequality. -/

theorem AvramDividend.Classical.avram_wave4_05_source_largejump_weighted_section_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 1 ≤ r) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
        (X.ψ θ - q)⁻¹ := by sorry
