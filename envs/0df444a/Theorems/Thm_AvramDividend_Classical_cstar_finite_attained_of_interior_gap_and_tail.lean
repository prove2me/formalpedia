-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_attained_of_interior_gap_and_tail
-- name    : AvramDividend.Classical.cstar_finite_attained_of_interior_gap_and_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:36:02.37521+00:00
-- url     : https://prove2.me/theorems/42c4386c-1325-43ee-9189-9ba08df010da
-- title:
--   Finite attained optimal dividend barrier from derivative continuity, strict interior improvement and tail lower bound
-- statement:
--   Suppose the scale-function derivative is continuous on the nonnegative half-line. If some strictly positive point a has a strictly smaller derivative than at zero, and sufficiently far along the positive half-line the derivative is no smaller than at a, then the canonical infimum-defined barrier cstar is finite and itself is a strictly positive global derivative minimiser. No separate minimum-attainment, set-compactness or positivity hypotheses are required.
-- source:
--   The pinned extreme-value theorem yields a positive global minimiser b from derivative continuity, strict interior improvement and eventual cocompact tail lower bound. Global minimality gives deriv W b <= deriv W a < deriv W 0. Apply the standalone continuous-derivative strict-boundary-gap attainment lemma to b and the previously submitted cstar_lt_top_of_minimizer to conclude both finite cstar and attained minimum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_attained_of_interior_gap_and_tail
    (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : 0 < a) (hgap : deriv W a < deriv W 0)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici (0 : ℝ)),
      deriv W a ≤ deriv W x) :
    cstar W < ⊤ ∧ (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
