-- Prove2me | Theorems.Thm_BroughanRH_ariasTaylor
-- name    : BroughanRH.ariasTaylor
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:23:32.879026+00:00
-- url     : https://prove2.me/theorems/539061d7-53ce-4f44-90f1-574f1adfc447
-- title:
--   Square summability of the transformed zeta-log coefficients
-- statement:
--   In the coordinate $z=(s-1)/s$, the Taylor coefficients at zero of $\log((s-1)\zeta(s))$ are square-summable. The removable value at $z=0$ is fixed explicitly. [Source](https://personal.us.es/arias/56-2RHB.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem ariasTaylor :
    let f (z : ℂ) := if z = 0 then 0 else Complex.log
      (((1-z)⁻¹ - 1)*riemannZeta ((1-z)⁻¹))
    Summable (fun n : ℕ => ‖iteratedDeriv n f 0/(n.factorial : ℂ)‖^2) := by sorry

end BroughanRH
