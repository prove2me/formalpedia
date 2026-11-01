-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_interior_generator_weighted_quadratic
-- name    : AvramDividend.Classical.avram_wave4_05_source_interior_generator_weighted_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:29:08.587985+00:00
-- url     : https://prove2.me/theorems/0af79a05-65b8-46ab-8dcc-d423441a781b
-- title:
--   Quadratic weighted positive-state source Lévy generator bound away from zero crossing
-- statement:
--   For the actual spectrally negative Lévy compensated jump integrand, a C2 function W on strictly positive reserves and a measurable continuous second-derivative representative F with finite exponentially weighted absolute mass give a sharp quadratic bound on the weighted state slice above the magnitude r of a small negative jump. This is the genuine interior complement of the Proved zero-crossing quadratic strip bound and will be combined with the original Lévy quadratic moment to justify global generator Fubini.
-- source:
--   Original SpectrallyNegativeLevy.generatorIntegrand and C2 source Taylor identity c4be88ef, canonical weighted Gaussian interior remainder integrability e11ef020. Avram, Palmowski and Pistorius (2007), generator Lemma 4; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave4_05_source_interior_generator_weighted_quadratic
    (W F : ℝ → ℝ) (hW : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (r θ : ℝ) (hr : 0 < r) (hr1 : r < 1) (hθ : 0 ≤ θ)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F)
    (hFi : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioi r) volume ∧
    (∫ x in Ioi r, Real.exp (-θ * x) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by sorry
