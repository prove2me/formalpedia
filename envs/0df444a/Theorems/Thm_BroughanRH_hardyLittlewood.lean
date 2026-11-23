-- Prove2me | Theorems.Thm_BroughanRH_hardyLittlewood
-- name    : BroughanRH.hardyLittlewood
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:31.321843+00:00
-- url     : https://prove2.me/theorems/f3ba5129-0000-45ad-8b09-d8225780876f
-- title:
--   Hardy–Littlewood’s series estimate
-- statement:
--   The series or sequence displayed in the formal statement is $O_\varepsilon(x^{-1/4+\varepsilon})$ as $x\to\infty$ for every $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 2.5. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem hardyLittlewood :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun x : ℝ => ∑' k : ℕ, ((-1 : ℝ)^(k+1) * x^(k+1)) / (((k+1).factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ) + 1)).re)) (fun x : ℝ => (x : ℝ) ^ (-(1 / 4) + ε)) := by sorry

end BroughanRH
