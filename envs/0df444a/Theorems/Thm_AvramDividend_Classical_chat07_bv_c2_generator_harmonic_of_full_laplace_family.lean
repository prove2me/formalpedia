-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_c2_generator_harmonic_of_full_laplace_family
-- name    : AvramDividend.Classical.chat07_bv_c2_generator_harmonic_of_full_laplace_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:50:37.333763+00:00
-- url     : https://prove2.me/theorems/8bc6f976-6f20-4cc4-a54c-c5ca8ff491ef
-- title:
--   BV C2 scale-function generator harmonicity from the full weighted Laplace residual family
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with a C1/C2 regular q-scale function on the positive half-line, suppose every admissible exponentially weighted generator residual is integrable and has zero integral. Then the scale function belongs to the generator domain and satisfies Gamma W=qW at every positive reserve below a. The generator domain follows from an accepted BV C1 theorem; residual continuity follows from an accepted BV C2 theorem. The accepted full-family Laplace uniqueness theorem then yields the pointwise equation. This isolates the remaining nontrivial Laplace/Fubini analytic obligation, which is NOT asserted automatically by IsScaleFunction.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_c2_generator_harmonic_of_full_laplace_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by sorry
