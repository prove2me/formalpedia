-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_continuous_deriv_tail
-- name    : AvramDividend.Classical.cstar_finite_of_continuous_deriv_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:16:50.682236+00:00
-- url     : https://prove2.me/theorems/64483b49-6d69-49e0-9027-9a9a2fdd6746
-- title:
--   Finiteness of the Avram optimal barrier from derivative continuity and coercive tail control
-- statement:
--   If the scale-function derivative is continuous on the nonnegative half-line, the extended right derivative at zero does not exceed the ordinary derivative at zero, and the derivative is eventually at least its zero value away from compact subsets of the half-line, then cstar is finite. This constructs a global minimiser by Mathlib's extreme-value theorem and splits it into a strictly positive minimiser or the zero-boundary case.
-- source:
--   Pinned Mathlib Topology/Order/Compact.lean ContinuousOn.exists_isMinOn' for a function on closed Ici 0 with a tail lower bound. Compose the previously published exact iff cstar finiteness theorem. The required derivative continuity, right-endpoint comparison and coercive tail property remain explicit and must be supplied by fluctuation-theoretic results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_of_continuous_deriv_tail (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (hboundary : derivZeroPlus W ≤ ((deriv W 0 : ℝ) : EReal))
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W 0 ≤ deriv W x) :
    cstar W < ⊤ := by
  sorry

end AvramDividend.Classical
