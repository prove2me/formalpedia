-- Prove2me | Theorems.Thm_BroughanRH_riesz
-- name    : BroughanRH.riesz
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:20:34.479784+00:00
-- url     : https://prove2.me/theorems/79297822-70c5-495d-ac5b-ffa6bb99bd83
-- title:
--   Riesz’s growth estimate
-- statement:
--   The series or sequence displayed in the formal statement is $O_\varepsilon(x^{1/4+\varepsilon})$ as $x\to\infty$ for every $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 2.4. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem riesz :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun x : ℝ => ∑' k : ℕ, ((-1 : ℝ)^k * x^(k+1)) / ((k.factorial : ℝ) * (riemannZeta (2 * (k+1 : ℂ))).re)) (fun x : ℝ => (x : ℝ) ^ (1 / 4 + ε)) := by sorry

end BroughanRH
