-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_interior_anchor_bounds
-- name    : AvramDividend.Classical.cstar_finite_of_interior_anchor_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T18:06:58.719084+00:00
-- url     : https://prove2.me/theorems/c9ed70d2-4fcc-4a2d-b050-cb05b2bceba0
-- title:
--   Finite optimal dividend barrier from positive interior anchor, near-zero bound and tail coercivity
-- statement:
--   Fix an interior anchor a>0 for W'. If the derivative is continuous on [a,∞), never falls below W'(a) on (0,a], and eventually stays at least W'(a) outside a compact subset of [a,∞), then it attains a global minimum at some positive point b, so cstar is finite. Crucially, unlike the continuous-on-[0,∞) finiteness criterion, this proof makes NO continuity, finite derivative or derivative-comparison assumption at 0 and therefore can apply when W'(0+) is infinite (the unbounded-variation, non-Gaussian branch).
-- source:
--   Uses pinned Mathlib ContinuousOn.exists_isMinOn' on closed halfline [a,∞), with the tail hypothesis coercive relative to derivative at anchor a. The attained b>=a minimizes derivative on [a,∞). In the open interval (0,a), hnear and minimality at a imply W'(b)<=W'(x); hence b∈cstarSet and Proved cstar_lt_top_of_minimizer yields finiteness. This avoids right-derivative regularity at zero required by previous child.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped ENNReal

namespace AvramDividend.Classical
theorem cstar_finite_of_interior_anchor_bounds (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ici a))
    (hnear : ∀ x : ℝ, 0 < x → x ≤ a → deriv W a ≤ deriv W x)
    (htail : ∀ᶠ x : ℝ in
      Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici a),
      deriv W a ≤ deriv W x) :
    cstar W < ⊤ := by
  sorry
end AvramDividend.Classical
