-- Prove2me | Theorems.Thm_BroughanRH_voros
-- name    : BroughanRH.voros
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:47.370724+00:00
-- url     : https://prove2.me/theorems/511cd3d7-4f87-4d53-bd88-4d2e3fbd8a3e
-- title:
--   Voros’s asymptotic formula for the Li coefficients
-- statement:
--   For the positive-index Li coefficient $L_n$, the quotient of $L_n$ by $n(\log n+\gamma-\log(2\pi)-1)/2$ tends to one. [Source](https://arxiv.org/abs/math/0506326).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem voros :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    let L (m : ℕ) : ℝ := ((iteratedDeriv (m+1) (fun s : ℂ => s^m * Complex.log (xi s)) 1)/(m.factorial : ℂ)).re
    Filter.Tendsto (fun m : ℕ => L m / (((m+1 : ℕ):ℝ) *
      (Real.log ((m+1 : ℕ):ℝ) + Real.eulerMascheroniConstant - Real.log (2*Real.pi) - 1)/2))
      Filter.atTop (nhds 1) := by sorry

end BroughanRH
