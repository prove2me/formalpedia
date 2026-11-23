-- Prove2me | Theorems.Thm_BroughanRH_ariasKeiper
-- name    : BroughanRH.ariasKeiper
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:53.460784+00:00
-- url     : https://prove2.me/theorems/77d5461b-f81e-4521-81b8-d78ff6b3ed92
-- title:
--   Arias de Reyna’s square-summable Keiper errors
-- statement:
--   The errors after subtracting $(\log n+\gamma-\log(2\pi)-1)/2$ from the Keiper coefficient $L_n/n$ are square-summable. [Source](https://doi.org/10.7169/facm/1317045228).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §4.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem ariasKeiper :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    let L (m : ℕ) : ℝ := ((iteratedDeriv (m+1) (fun s : ℂ => s^m * Complex.log (xi s)) 1)/(m.factorial : ℂ)).re
    Summable (fun m : ℕ => (L m / ((m+1 : ℕ):ℝ) -
      (Real.log ((m+1 : ℕ):ℝ) + Real.eulerMascheroniConstant - Real.log (2*Real.pi) - 1)/2)^2) := by sorry

end BroughanRH
