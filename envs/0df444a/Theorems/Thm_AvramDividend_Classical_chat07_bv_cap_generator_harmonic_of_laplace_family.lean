-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_cap_generator_harmonic_of_laplace_family
-- name    : AvramDividend.Classical.chat07_bv_cap_generator_harmonic_of_laplace_family
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:15:50.052979+00:00
-- url     : https://prove2.me/theorems/328de415-a555-4b6a-9e05-dc950631eda7
-- title:
--   BV dividend cap q-harmonicity from the full scale residual Laplace family
-- statement:
--   For a standing bounded-variation spectrally negative Levy process with no Gaussian part, positive canonical barrier and positive discount, assume the scale function is C1/C2 on positive reserves, differentiable with nonzero derivative at the barrier, and its generator residual has an integrable zero Laplace transform for every admissible Laplace parameter. Then the full nonlocal dividend-value generator is integrable and harmonic at the barrier. This combines the accepted full-family Laplace interior scale harmonicity reduction with the accepted BV cap transfer, removing a separate interior q-harmonicity hypothesis. The weighted residual family remains an explicit nontrivial analytic premise.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_cap_generator_harmonic_of_laplace_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
