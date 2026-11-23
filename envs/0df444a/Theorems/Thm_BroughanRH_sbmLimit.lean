-- Prove2me | Theorems.Thm_BroughanRH_sbmLimit
-- name    : BroughanRH.sbmLimit
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:25:13.580817+00:00
-- url     : https://prove2.me/theorems/e7cba228-26f8-4aad-8fd3-f34aeeea9533
-- title:
--   The limiting Poisson-weighted zeta identity
-- statement:
--   For $1/2\le b<1$, the integral of the log modulus against the Poisson weight with parameter $1-b$ equals $-\log(2-2b)$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 8.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem sbmLimit :
    ∀ b : ℝ, 1/2 ≤ b → b < 1 →
      let f (t : ℝ) := Real.log ‖riemannZeta ((b : ℂ)+(t : ℂ)*Complex.I)‖/((1-b)^2+t^2)
      MeasureTheory.Integrable f ∧ ((1-b)/Real.pi)*(∫ t : ℝ, f t) = -Real.log (2-2*b) := by sorry

end BroughanRH
