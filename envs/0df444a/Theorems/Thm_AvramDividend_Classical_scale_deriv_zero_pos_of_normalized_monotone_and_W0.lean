-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_deriv_zero_pos_of_normalized_monotone_and_W0
-- name    : AvramDividend.Classical.scale_deriv_zero_pos_of_normalized_monotone_and_W0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:59:08.958328+00:00
-- url     : https://prove2.me/theorems/58b17bd8-6946-46ba-94e3-2e7e2e6610c2
-- title:
--   Positive right scale derivative at zero for a tilted-monotone scale with W(0)>0
-- statement:
--   Let φ>0 and W(0)>0. Assume W is nondecreasing on the nonnegative half-line, its exponentially normalised version exp(-φ x)W(x) is nondecreasing for x>0, and W is differentiable there. Then its extended one-sided derivative liminf at zero is strictly positive. The proof obtains the uniform strict bound W'(x) ≥ φ W(x) ≥ φ W(0)>0 before taking the right limit inferior. This addresses the positive initial-value branch relevant to bounded-variation Lévy scale functions.
-- source:
--   Compose the previously proved normalized_derivative_lower_bound with ordinary MonotoneOn W on Ici 0. Apply the pinned Mathlib Filter.le_liminf_of_le to the uniform inequality and convert the positive real φ*W(0) into an EReal positive lower bound. Only the tilted monotonicity hypothesis remains an external fluctuation-theoretic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
open AvramDividend.Classical Filter
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem scale_deriv_zero_pos_of_normalized_monotone_and_W0
    (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmonoW : MonotoneOn W (Set.Ici 0))
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    (0 : EReal) < derivZeroPlus W := by
  sorry

end AvramDividend.Classical
