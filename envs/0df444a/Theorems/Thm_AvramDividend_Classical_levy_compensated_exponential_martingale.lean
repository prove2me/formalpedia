-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
-- name    : AvramDividend.Classical.levy_compensated_exponential_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:23:51.973976+00:00
-- url     : https://prove2.me/theorems/b707e3a2-56a3-4a7b-af9e-53cba9e3731b
-- title:
--   Laplace-compensated exponential of a spectrally negative Lévy process is a martingale
-- statement:
--   For any nonnegative Laplace parameter θ, the process Z_t=exp(θX_t−tψ(θ)) is a martingale in the mission's original filtration. It is adapted by measurability, integrable by the Laplace transform, and its future increment factor has conditional expectation one. The exponential factorization Z_t=Z_s*g_{s,t} and Mathlib's conditional expectation pull-out theorem give E[Z_t|𝓕_s]=Z_s. Neither boundedness of the adapted factor nor any Itô theorem is assumed.
-- source:
--   Direct consequence of SpectrallyNegativeLevy independent stationary increments, Laplace transform, and Mathlib condExp_mul_of_aestronglyMeasurable_left, through the published analytic and probabilistic helper lemmas. Useful foundation for the generator-to-martingale part of AvramDividend.Classical.local_verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_exponential_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Martingale (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) 𝓕 P := by sorry
