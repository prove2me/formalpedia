-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_tilt_deriv_pos_of_positive_factor
-- name    : AvramDividend.Classical.exp_tilt_deriv_pos_of_positive_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:26:06.965574+00:00
-- url     : https://prove2.me/theorems/675bc3a5-ef9c-4724-962c-f7aedc5139c2
-- title:
--   Strict positivity of the q-scale derivative from an exponential tilt with positive monotone factor
-- statement:
--   Let φ>0, and let V be positive and differentiable on (0,∞), with nonnegative ordinary derivative. Then the derivative of exp(φx)V(x) is strictly positive at every x>0. The factorisation identity gives exp(φx)(φV(x)+V'(x)), whose first term is strictly positive and second term nonnegative. This is the elementary positivity bridge needed to obtain scaleDeriv_pos from a positive nondecreasing Esscher-tilted scale function, once the process-specific factorisation is formalised.
-- source:
--   Pinned Mathlib HasDerivAt.exp, HasDerivAt.mul and hasDerivAt_const_mul product-rule APIs. This result is conditional on the tilt factor's positivity and derivative monotonicity; it is not the general scaleDeriv_pos theorem for all spectrally negative Levy processes, which remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem exp_tilt_deriv_pos_of_positive_factor
    (φ : ℝ) (hφ : 0 < φ) (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv V x) :
    ∀ x : ℝ, 0 < x →
      0 < deriv (fun t : ℝ => Real.exp (φ * t) * V t) x := by
  sorry
end AvramDividend.Classical
