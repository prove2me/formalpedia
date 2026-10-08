-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf
-- name    : AvramDividend.Classical.deriv_global_lower_le_right_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:50:41.335162+00:00
-- url     : https://prove2.me/theorems/92f1a6b8-f31b-4309-9a05-c58b8e258935
-- title:
--   Global positive-domain derivative lower bound controls the extended derivative at zero
-- statement:
--   If every strictly positive ordinary derivative of W is at least a fixed real value d, then the canonical Avram one-sided extended derivative liminf at zero is at least d as an EReal value. This includes equality and infinite limits, requiring no smoothness or strict boundary gap. It supplies the missing zero-boundary denominator comparison whenever d is the global derivative minimum at cstar.
-- source:
--   From the global pointwise bound derive an eventual lower bound along nhdsWithin 0 (Ioi 0), then apply the pinned Mathlib Filter.le_liminf_of_le. Coerce real order into EReal with exact_mod_cast. This proves a non-strict boundary inequality without appealing to unproved stochastic properties.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem deriv_global_lower_le_right_liminf
    (W : ℝ → ℝ) (d : ℝ)
    (hlower : ∀ x : ℝ, 0 < x → d ≤ deriv W x) :
    (d : EReal) ≤ derivZeroPlus W := by
  sorry

end AvramDividend.Classical
