-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian_jump_integrable
-- name    : AvramDividend.Classical.psi_eventually_gt_of_gaussian_jump_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:34:30.458979+00:00
-- url     : https://prove2.me/theorems/74cf887f-0ead-4dfa-bd46-7404dcb08f35
-- title:
--   Eventual positive Lévy exponent from Gaussian coefficient and negative-jump integrability
-- statement:
--   A spectrally negative Lévy exponent with strictly positive Gaussian coefficient exceeds any fixed discount rate for every sufficiently large Laplace parameter, provided the negative-jump integrand is integrable and the large-jump mass is finite. This assembles the Gaussian branch of exponent divergence with exactly the two remaining Lévy-measure requirements explicit.
-- source:
--   The Gaussian term supplies a positive quadratic coefficient. The integrated jump-kernel lower bound controls the negative-jump correction by a finite constant, and the elementary positive-quadratic lemma supplies an eventual threshold. Both supporting theorems are separate proof children; remote acceptance of this parent may initially be only SKETCH_ACCEPTED.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem psi_eventually_gt_of_gaussian_jump_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hσ : 0 < X.σ)
    (hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) (Iio (0 : ℝ)) X.ν) :
    ∃ β0 : ℝ, 0 ≤ β0 ∧
      ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ := by
  sorry

end AvramDividend.Classical
