-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_crossing_weighted_quadratic
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_crossing_weighted_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:46:32.67713+00:00
-- url     : https://prove2.me/theorems/ca3bd231-5959-4364-bbe1-93cadd6fab54
-- title:
--   Weighted quadratic crossing-strip estimate for the original Gaussian Levy generator
-- statement:
--   For the original spectrally negative Lévy process with Standing and a Gaussian component, its compensated negative-jump generator crossing strip x in (0,-y) admits an exponentially weighted absolute integral dominated by C y^2 uniformly in every θ≥0 and -1<y<0. This derives from the proved source crossing quadratic bound, compact-strip integrability of an exponential multiplier, and monotonicity of the set integral.
-- source:
--   Exact source generatorIntegrand, source Gaussian crossing-strip quadratic theorem proved 30 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_source_crossing_quadratic_strip

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_crossing_weighted_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ : ℝ, 0 ≤ θ →
      ∀ y : ℝ, -1 < y → y < 0 →
        IntegrableOn
          (fun x : ℝ => Real.exp (-(θ * x)) *
            |SpectrallyNegativeLevy.generatorIntegrand W x y|)
          (Ioo (0 : ℝ) (-y)) ∧
        (∫ x in Ioo (0 : ℝ) (-y),
          Real.exp (-(θ * x)) *
            |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤
          C * y ^ 2 := by sorry
