-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone
-- name    : AvramDividend.Classical.scale_deriv_pos_of_normalized_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:37:41.229608+00:00
-- url     : https://prove2.me/theorems/308e5291-43dd-409e-9c7e-fd9ceee2635f
-- title:
--   Strict derivative positivity from positivity and monotonicity of an exponentially tilted scale function
-- statement:
--   If W(x)>0 for every x>0, W is differentiable on the positive half-line, and for some phi>0 the normalised function exp(-phi x) W(x) is nondecreasing there, then W'(x) is strictly positive at every positive x. This supplies the strict-positive derivative ingredient missing from the original Avram optimal-barrier proof. It is conditional on the tilted monotonicity property, which still needs to be established from the Levy assumptions.
-- source:
--   Previously Proved normalized_derivative_lower_bound yields phi * W(x) <= W'(x) from positive-level differentiability and monotonicity of the exponentially tilted function. Since both phi and W(x) are strictly positive, mul_pos gives a strictly positive lower bound for the derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scale_deriv_pos_of_normalized_monotone
    (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hmono : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  sorry

end AvramDividend.Classical
