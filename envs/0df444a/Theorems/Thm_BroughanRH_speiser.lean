-- Prove2me | Theorems.Thm_BroughanRH_speiser
-- name    : BroughanRH.speiser
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:19:40.002347+00:00
-- url     : https://prove2.me/theorems/4eaed843-507f-4415-bb09-b548927bc5d9
-- title:
--   Speiser’s zero-free half-strip for the derivative
-- statement:
--   The derivative of zeta has no zeros in the open half-strip $0<\Re(s)<1/2$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.16. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem speiser :
    ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → deriv riemannZeta s ≠ 0 := by sorry

end BroughanRH
