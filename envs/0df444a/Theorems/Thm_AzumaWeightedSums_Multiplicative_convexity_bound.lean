-- Prove2me | Theorems.Thm_AzumaWeightedSums_Multiplicative_convexity_bound
-- name    : AzumaWeightedSums.Multiplicative.convexity_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:42.457874+00:00
-- url     : https://prove2.me/theorems/54137607-334a-4e74-b3ff-924dbf8d3276
-- title:
--   (2.2), corrected: exponential convexity bound
-- statement:
--   For real $t$, nonzero real $b$, and $x\in[-1,1]$, convexity gives the corrected form of Azuma's display (2.2):
--
--   $$
--   e^{tbx}\le\cosh(t|b|)+\frac{bx}{|b|}\sinh(t|b|).
--   $$
--
--   This pointwise inequality is the deterministic step used to control the moment-generating function of a bounded multiplicative system.
--
--   **Formalization Note** The printed display has $x/|b|$ in the linear term. The missing factor $b$ makes the printed inequality false, for example at $t=x=1$ and $b=2$; the Lean statement records the corrected inequality.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), pp. 357–358, §2, proof of Lemma 1, (2.2), corrected, https://doi.org/10.2748/tmj/1178243286

import Mathlib

namespace AzumaWeightedSums.Multiplicative

/-- The corrected form of Azuma (1967), p. 358, (2.2). The printed linear term
omits the factor `b`. -/
theorem convexity_bound (t b x : ℝ) (hb : b ≠ 0) (hx : |x| ≤ 1) :
    Real.exp (t * b * x) ≤
      Real.cosh (t * |b|) + (b * x / |b|) * Real.sinh (t * |b|) := by sorry

end AzumaWeightedSums.Multiplicative
