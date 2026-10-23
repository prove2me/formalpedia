-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
-- name    : AvramDividend.Classical.gaussian_esscher_volterra_kernel_equation_of_positive_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:11:25.653371+00:00
-- url     : https://prove2.me/theorems/9d9714d3-ad96-479d-a82e-1561ae45c43e
-- title:
--   Gaussian Esscher scale function satisfies an integrated causal Volterra equation
-- statement:
--   At a positive Esscher root and positive Gaussian coefficient, the tilted scale V satisfies a second-kind causal integrated Volterra identity with a>0 and K in L1(0,infinity): aV(x)+∫_0^x(β+K(x-s))V(s)ds=x. The Gaussian Levy-Khintchine Laplace denominator identity and scale-function transform give equality of Laplace transforms, and signed uniqueness identifies the continuous representatives. Near-origin boundedness of V is intentionally separated into the independently provable Gaussian monotonicity lemma.
-- source:
--   Proved gaussian_esscher_root_volterra_denominator and esscher_tilted_scale_laplace_shift, Fourier-Laplace convolution inversion and signed uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_volterra_kernel_equation_of_positive_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) := by sorry
