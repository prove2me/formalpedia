-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_matched_overlap_ne_puncture
-- name    : BraidsLinksMCG.puncturedPlane_matched_overlap_ne_puncture
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T08:47:41.790813+00:00
-- url     : https://prove2.me/theorems/7f6a5aaf-5ecf-41e4-b810-9dd7f701625f
-- title:
--   No point of the matched-cover overlap is a puncture
-- statement:
--   No point of the matched-cover overlap is a puncture.  A puncture of the plane punctured at the first $n+1$ positive integers is the real complex point $j+1$ for $j : \mathrm{Fin}(n+1)$, and every puncture is real.  The overlap requires the real part to exceed $n+1-\tfrac34$, which places $j$ above $n-\tfrac74$; since $j$ is an integer strictly below $n+1$, the only possibility is $j=n$, so the only candidate puncture is the real point $n+1$.  That point has real part exactly $n+1$, so it fails the first disjunct; it has imaginary part $0$, so it fails the second; and it lies at distance exactly $1$ from the anchor $n+2$, so it fails the third.  This child isolates the puncture-exclusion obligation needed to transport contractibility from the overlap region to the punctured plane.
-- source:
--   Direct planar geometry of the two-region matched cover of the plane punctured at the first n+1 positive integers: the overlap corridor's real lower bound n+1-3/4 singles out the final puncture n+1, which is real, lies exactly one to the left of the anchor n+2, and therefore satisfies none of the three cap disjuncts.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem puncturedPlane_matched_overlap_ne_puncture (n : ℕ) (j : Fin (n + 1))
    (hlo : (n : ℝ) + 1 - 3 / 4 < (((j : ℕ) + 1 : ℕ) : ℂ).re)
    (hcap : (((j : ℕ) + 1 : ℕ) : ℂ).re < (n : ℝ) + 1 ∨
      0 < (((j : ℕ) + 1 : ℕ) : ℂ).im ∨
      dist (((j : ℕ) + 1 : ℕ) : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) : False := by sorry

end BraidsLinksMCG
