-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_bv_C1_weighted
-- name    : AvramDividend.Classical.scaleFunction_generator_interval_harmonic_of_bv_C1_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:28:45.203143+00:00
-- url     : https://prove2.me/theorems/2c9c19c1-19f5-4373-9dda-026e2d110089
-- title:
--   Bounded-variation C1 scale-function generator harmonicity from the weighted Laplace family on any positive interval
-- statement:
--   For a standing BV spectrally negative Levy process with q>0 and q-scale function W, if the full family of weighted generator-residual Laplace integrals is zero and the generator is integrable on (0,a), then the residual is identically zero on (0,a). Bounded variation makes sigma vanish. Proved C1 scale regularity and positive-half-line generator continuity supply the hypotheses of the Proved Laplace-uniqueness interval theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, BV first-order generator and uniqueness of its weighted Laplace residual.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_interval_harmonic_of_bv_C1_weighted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
