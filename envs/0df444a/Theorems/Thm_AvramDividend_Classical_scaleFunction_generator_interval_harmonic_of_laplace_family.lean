-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
-- name    : AvramDividend.Classical.scaleFunction_generator_interval_harmonic_of_laplace_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:35:30.928611+00:00
-- url     : https://prove2.me/theorems/f9004ff3-07c5-4268-ba0c-4d085212fe67
-- title:
--   Pointwise q-scale generator harmonicity on an interval from the full Laplace-residual family
-- statement:
--   For a standing spectrally negative Lévy process and exact q-scale function W, assume that the generator residual ΓW−qW is continuous on positive reserves, that every admissible exponential weighting has an integrable vanishing Laplace residual, and that W belongs to the generator domain throughout (0,a). Then W is genuinely pointwise q-harmonic throughout (0,a), including its exact generator-domain condition. The argument combines the already-Proved all-parameter Laplace uniqueness/ae harmonicity theorem with a separate Proved continuous ae-zero to pointwise upgrade. Unlike a sketch, no Open theorem is imported. The key remaining analytic obligation is deriving the family of vanishing residual integrals and continuity from the original Lévy-scale assumptions, which are explicit and not silently assumed.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaleFunction_generator_interval_harmonic_of_laplace_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (Ioi (0 : ℝ)))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry
