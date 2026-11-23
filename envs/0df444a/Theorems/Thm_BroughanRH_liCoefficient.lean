-- Prove2me | Theorems.Thm_BroughanRH_liCoefficient
-- name    : BroughanRH.liCoefficient
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:58.486532+00:00
-- url     : https://prove2.me/theorems/507e86a9-63f2-4553-9cea-8742298613ee
-- title:
--   Li’s coefficient criterion
-- statement:
--   Every positive-index Li coefficient is nonnegative, in the logarithmic-derivative normalization of Li’s criterion. [Source](https://github.com/artifish26/riemann-hypothesis-lean/blob/main/CLAIMS.md).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.5. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem liCoefficient :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ n : ℕ, 0 ≤ ((iteratedDeriv (n+1) (fun s : ℂ => s^n * Complex.log (xi s)) 1) / (n.factorial : ℂ)).re := by sorry

end BroughanRH
