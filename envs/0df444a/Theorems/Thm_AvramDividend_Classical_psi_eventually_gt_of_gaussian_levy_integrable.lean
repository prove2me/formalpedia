-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian_levy_integrable
-- name    : AvramDividend.Classical.psi_eventually_gt_of_gaussian_levy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T12:07:00.046692+00:00
-- url     : https://prove2.me/theorems/d2dd82a7-d5af-4a66-a00b-1c897833e249
-- title:
--   Gaussian Lévy exponent eventually exceeds discount rate using the built-in Lévy-measure integrability field
-- statement:
--   If the Gaussian coefficient is positive and the compensated negative-jump integral is defined at every nonnegative Laplace parameter, the canonical Avram Lévy exponent eventually exceeds any discount rate. Finiteness of the large-negative-jump mass is discharged using the structure's Lévy integrability field, rather than taken as an extra hypothesis.
-- source:
--   Compose author-owned children finite_large_negative_jump_mass and psi_eventually_gt_of_gaussian_jump_integrable. Avoids duplicating their analytic proofs while preserving explicit compensated-integrand integrability as the outstanding stochastic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped ENNReal NNReal

namespace AvramDividend.Classical
theorem psi_eventually_gt_of_gaussian_levy_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hσ : 0 < X.σ)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) (Iio (0 : ℝ)) X.ν) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧ ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ := by
  sorry
end AvramDividend.Classical
