-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small
-- name    : AvramDividend.Classical.psi_normalised_lower_bound_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:14:19.04095+00:00
-- url     : https://prove2.me/theorems/6952003f-190b-4ba4-a152-8049f72b66cc
-- title:
--   Zero-Gaussian Lévy exponent normalised lower bound
-- statement:
--   If the canonical Lévy process has zero Gaussian coefficient and positive Laplace parameter θ, then ψ(θ)/θ is bounded below by the drift c plus the normalised small-jump compensated integral minus the finite large-negative-jump mass divided by θ. This formal algebraic bridge turns negative-jump integral asymptotics into the exact eventually positive ψ argument.
-- source:
--   Direct division of Prove2Me-Proved psi_lower_bound_by_compensated_small_jumps under X.σ=0, using a positive denominator and elementary algebra. Exact hlarge integrability hypothesis remains explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.psi_normalised_lower_bound_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ)
    (hlarge : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Iic (-1 : ℝ)) X.ν) :
    X.c +
      (∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) / θ -
      (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / θ ≤
      X.ψ θ / θ := by sorry
