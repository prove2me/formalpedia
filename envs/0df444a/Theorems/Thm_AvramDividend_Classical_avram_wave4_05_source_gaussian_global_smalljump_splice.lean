-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_global_smalljump_splice
-- name    : AvramDividend.Classical.avram_wave4_05_source_gaussian_global_smalljump_splice
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:49:36.859797+00:00
-- url     : https://prove2.me/theorems/e7ad158f-c973-4ab3-a9c0-f524121406c0
-- title:
--   Complete positive-reserve weighted quadratic bound for compensated Gaussian small jumps
-- statement:
--   For the original Gaussian spectrally negative Levy process and original q-scale function, a measurable positive-half-line curvature representative with finite exponentially weighted L1 mass controls the true compensated generatorIntegrand uniformly in the small negative jump magnitude across all positive reserves. This theorem rigorously glues the crossing strip 0<x<r and positive interior x>r, treats the single reserve x=r as a Lebesgue null point, and yields a state-weighted integral bound (C+Mθ/2)r², uniform for 0<r<1. This is the source small-jump section domination required for Levy-measure quadratic-moment Fubini.
-- source:
--   Crossing source Gaussian weighted quadratic ca3bd231, source interior weighted quadratic 0af79a05, Mathlib setIntegral_union and singleton-null identities, pinned Mathlib 0df444a. Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_crossing_weighted_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_interior_generator_weighted_quadratic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual compensated source kernel, crossing and interior joined on every
    positive reserve, with the true Gaussian source crossing coefficient. -/

theorem AvramDividend.Classical.avram_wave4_05_source_gaussian_global_smalljump_splice
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (F : ℝ → ℝ)
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hFm : Measurable F) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ : ℝ, 0 ≤ θ →
        Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume →
        ∀ r : ℝ, 0 < r → r < 1 →
          IntegrableOn
            (fun x : ℝ => Real.exp (-θ * x) *
              |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
            (Ioi (0 : ℝ)) volume ∧
          (∫ x in Ioi (0 : ℝ),
            Real.exp (-θ * x) *
              |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
            (C + (∫ u : ℝ, Real.exp (-θ * u) * |F u|) / 2) * r ^ 2 := by sorry
