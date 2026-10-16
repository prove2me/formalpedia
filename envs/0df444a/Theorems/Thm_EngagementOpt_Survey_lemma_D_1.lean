-- Prove2me | Theorems.Thm_EngagementOpt_Survey_lemma_D_1
-- name    : EngagementOpt.Survey.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:10.13167+00:00
-- url     : https://prove2.me/theorems/6150d17c-9eb4-4add-b02e-aa0f325e2a9d
-- title:
--   Lemma D.1: $\varphi(x)\ge\frac12$ for $x>0$ and $\varphi(x)\le\frac12$ for $-1<x<0$
-- statement:
--   Let $\varphi(x)=\dfrac{x+1}{x}\left(1-\dfrac{\ln(x+1)}{x}\right)$. Then
--
--   1. for every $x>0$,
--   $$
--   \frac{x+1}{x}\left(1-\frac{\ln(x+1)}{x}\right)\ge\frac12;
--   $$
--   2. for every $x$ with $-1<x<0$,
--   $$
--   \frac{x+1}{x}\left(1-\frac{\ln(x+1)}{x}\right)\le\frac12 .
--   $$
--
--   With $x=\beta^t-1$, this compares the growth rate of $\mathbb E[T_q\mid T=t]$ with the rate $1/2$ of the symmetric case $p=q$; it gives parts 2(a) and 3(a) of Theorem 5.1.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 40, Lemma D.1

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

namespace EngagementOpt.Survey

/-- arXiv:2202.11776v3, p. 40, Lemma D.1: `(x + 1)/x · (1 - ln(x + 1)/x) ≥ 1/2` for `x > 0`, and
`≤ 1/2` for `-1 < x < 0`. -/
theorem lemma_D_1 :
    (∀ x : ℝ, 0 < x → 1 / 2 ≤ phi x) ∧
    (∀ x : ℝ, -1 < x → x < 0 → phi x ≤ 1 / 2) := by sorry

end EngagementOpt.Survey
