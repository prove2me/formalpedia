-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_nearzero_and_tail_bounds
-- name    : AvramDividend.Classical.cstar_finite_of_nearzero_and_tail_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T18:09:20.167191+00:00
-- url     : https://prove2.me/theorems/c10c5d95-188d-428d-a68e-bc946069d2b0
-- title:
--   Global positive derivative minimum from near-zero and infinity lower bounds
-- statement:
--   Suppose W' is continuous on the open positive halfline (but may diverge at 0). Fix a>0 and thresholds 0<δ<a<M. If W'(x)≥W'(a) whenever 0<x<δ, and again whenever x>M, then W' attains a GLOBAL minimum b>0 by compactness on [δ,M], since its values outside the interval are no smaller than W'(a). Therefore cstar is finite. This reduces the unbounded-variation branch to two asymptotic derivative lower bounds without needing either regularity at the origin or derivative monotonicity on (0,a).
-- source:
--   Apply pinned Mathlib isCompact_Icc.exists_isMinOn to derivative restricted to closed interval [δ,M], which lies in (0,∞). Since a belongs to the interval, the global minimum is bounded above by derivative at a. Near-zero and large-x lower-bound assumptions control the complement. Positive minimizer belongs to cstarSet and the Proved cstar_lt_top_of_minimizer yields cstar finite. Mathematically this captures derivative divergence at both ends with no continuity assumption at x=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Set
open scoped ENNReal

namespace AvramDividend.Classical
theorem cstar_finite_of_nearzero_and_tail_bounds
    (W : ℝ → ℝ) (a δ M : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hδa : δ < a) (haM : a < M)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hnear : ∀ x : ℝ, 0 < x → x < δ →
      deriv W a ≤ deriv W x)
    (htail : ∀ x : ℝ, M < x → deriv W a ≤ deriv W x) :
    cstar W < ⊤ := by
  sorry
end AvramDividend.Classical
