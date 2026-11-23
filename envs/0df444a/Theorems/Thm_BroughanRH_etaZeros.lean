-- Prove2me | Theorems.Thm_BroughanRH_etaZeros
-- name    : BroughanRH.etaZeros
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:19:33.46073+00:00
-- url     : https://prove2.me/theorems/16a875d6-f15e-444a-a105-6977619d8e61
-- title:
--   Zeros of Dirichlet eta in the critical strip
-- statement:
--   Every zero of the Dirichlet eta function in the open critical strip has real part $1/2$. [Source](https://github.com/AlexKontorovich/Lean-RH).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.12. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem etaZeros :
    let eta (s : ℂ) := (1 - (2 : ℂ)^(1-s)) * riemannZeta s
    ∀ s : ℂ, 0 < s.re → s.re < 1 → eta s = 0 → s.re = 1/2 := by sorry

end BroughanRH
