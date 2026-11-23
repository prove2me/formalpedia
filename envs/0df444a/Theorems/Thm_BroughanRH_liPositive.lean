-- Prove2me | Theorems.Thm_BroughanRH_liPositive
-- name    : BroughanRH.liPositive
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:22:23.7034+00:00
-- url     : https://prove2.me/theorems/24a4bf0f-69b3-459d-aa5b-5061ac122508
-- title:
--   Strict positivity of every Li coefficient
-- statement:
--   Every positive-index Li coefficient is strictly positive. This card uses the derivative representation for the coefficient in Corollary 4.17.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Cor. 4.17. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem liPositive :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ n : ℕ, 0 < ((iteratedDeriv (n+1) (fun s : ℂ => s^n * Complex.log (xi s)) 1) / (n.factorial : ℂ)).re := by sorry

end BroughanRH
