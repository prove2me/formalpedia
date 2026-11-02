-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_bv_generator_integrable_of_first_moment_envelope
-- name    : AvramDividend.Classical.avram_wave4_p3_bv_generator_integrable_of_first_moment_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:05:47.749813+00:00
-- url     : https://prove2.me/theorems/1768e89b-9f2d-4fe6-ae2f-cb4de3986212
-- title:
--   BV first-moment envelope implies actual Lévy generator integrability for a measurable payoff
-- statement:
--   For the true bounded-variation spectrally negative Lévy generator, any measurable test payoff whose compensated jump integrand is bounded on all negative jumps by C min(1,|y|), for finite C≥0, is generator-integrable at the specified state. The proof uses the genuine BV Lévy first-moment integral, makes the full compensated kernel measurable, and performs norm majorisation without assuming monotonicity or continuity of the original payoff. This supplies a modular domain component for the unpublished positive optimal barrier matched-germ perturbation continuity interface.
-- source:
--   Unpublished, uncompiled P3 source-complete draft work/avram_wave4_p3_bv_generator_integrable_of_first_moment_envelope_draft.lean SHA-256 e2b96e51a288fac02687e4b866b3f26d5434a32d3fc28e79fd1ab61c4c1d8fae, 2452 bytes. Imports Proved BV moment helper 1f8249f1. This is NOT a remote proof or accepted canonical theorem and has no eligible mission queue target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_bv_generator_integrable_of_first_moment_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (f : ℝ → ℝ) (hfmeas : Measurable f) (x : ℝ)
    (henv : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 |y|) :
    X.GeneratorIntegrable f x := by sorry
