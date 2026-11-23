-- Prove2me | Theorems.Thm_BroughanRH_jensen
-- name    : BroughanRH.jensen
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:37.636027+00:00
-- url     : https://prove2.me/theorems/75df0cd3-f006-4b7b-a3be-ed4f30864af6
-- title:
--   Hyperbolicity of all xi Jensen polynomials
-- statement:
--   Every Jensen polynomial formed from the even central Taylor coefficients of xi has only real roots, for each degree and each shift. Multiplying the coefficient sequence by a fixed positive scalar leaves these polynomials’ roots unchanged. [Source](https://arxiv.org/abs/1910.01227).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 7.3; Ch. 8. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem jensen :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    let a (j : ℕ) : ℂ := (j.factorial : ℂ) * iteratedDeriv (2*j) xi (1/2) / ((2*j).factorial : ℂ)
    ∀ d n : ℕ, ∀ z : ℂ, (∑ j ∈ Finset.range (d+1), (d.choose j : ℂ) * a (n+j) * z^j) = 0 → z.im = 0 := by sorry

end BroughanRH
