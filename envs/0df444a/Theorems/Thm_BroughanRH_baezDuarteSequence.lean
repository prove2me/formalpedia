-- Prove2me | Theorems.Thm_BroughanRH_baezDuarteSequence
-- name    : BroughanRH.baezDuarteSequence
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:21:17.087529+00:00
-- url     : https://prove2.me/theorems/b3d3658f-2c1a-4fb1-b006-e660f4caf82e
-- title:
--   Báez-Duarte’s alternating binomial sum
-- statement:
--   The series or sequence displayed in the formal statement is $O_\varepsilon(x^{-3/4+\varepsilon})$ as $x\to\infty$ for every $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II §2.6. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem baezDuarteSequence :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun k : ℕ => ∑ j ∈ Finset.range (k+1), (-1 : ℝ)^j * (k.choose j : ℝ) / (riemannZeta (2 * (j : ℂ) + 2)).re) (fun x : ℕ => (x : ℝ) ^ (-(3 / 4) + ε)) := by sorry

end BroughanRH
