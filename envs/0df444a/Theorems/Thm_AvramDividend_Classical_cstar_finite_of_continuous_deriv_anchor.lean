-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_continuous_deriv_anchor
-- name    : AvramDividend.Classical.cstar_finite_of_continuous_deriv_anchor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:05:09.057722+00:00
-- url     : https://prove2.me/theorems/4d625df2-60de-4b7e-b2cb-0ac65d252276
-- title:
--   Finiteness of cstar from a compactly attained derivative minimum relative to an arbitrary nonnegative anchor
-- statement:
--   For any nonnegative reference point b, assume W' is continuous on [0,∞) and eventually W'(x) ≥ W'(b) away from compact subsets of the nonnegative halfline. Assume also that the extended right derivative at zero does not exceed the ordinary derivative at zero. Then W' attains a global minimum on [0,∞); either a positive minimizer exists, or 0 has the smallest derivative including the extended boundary value, and in both cases cstar is finite. This extends the existing b=0 theorem, allowing the derivative tail to be bounded by the value at an interior point even if W'(0) is larger.
-- source:
--   Pinned Mathlib/Topology/Order/Compact.lean ContinuousOn.exists_isMinOn' applied to s=Ici 0 and reference b, then the Proved AvramDividend.Classical.cstar_lt_top_iff_minimizer_or_zero_boundary. The earlier cstar_finite_of_continuous_deriv_tail fixed the reference point to zero and was proved; this child genuinely weakens that tail premise by permitting any nonnegative b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped ENNReal

namespace AvramDividend.Classical
theorem cstar_finite_of_continuous_deriv_anchor (W : ℝ → ℝ) (b : ℝ)
    (hb : 0 ≤ b)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (hboundary : derivZeroPlus W ≤ ((deriv W 0 : ℝ) : EReal))
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W b ≤ deriv W x) :
    cstar W < ⊤ := by
  sorry
end AvramDividend.Classical
