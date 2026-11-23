-- Prove2me | Theorems.Thm_BroughanRH_sbmOpen
-- name    : BroughanRH.sbmOpen
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:24:51.067005+00:00
-- url     : https://prove2.me/theorems/547e52eb-f42c-4ac3-95ff-09f45441179e
-- title:
--   Sekatskii–Beltraminelli–Merlini on the open half-strip
-- statement:
--   Use the logarithm of zeta continued from the right along each horizontal line. The integral of $\log\zeta(s)/s^2$ with respect to height, divided by $2\pi$, equals $1-1/b$ for $1/2<b<1$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 8.3. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem sbmOpen :
    let h (b t : ℝ) : ℂ := -(∫ u in Set.Ioi b, deriv riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I) / riemannZeta ((u : ℂ) + (t : ℂ)*Complex.I))
    ∀ b : ℝ, 1/2 < b → b < 1 →
      let f (t : ℝ) := h b t / ((b : ℂ) + (t : ℂ)*Complex.I)^2
      MeasureTheory.Integrable f ∧ (∫ t : ℝ, f t)/(2*(Real.pi : ℂ)) = 1 - 1/(b : ℂ) := by sorry

end BroughanRH
