-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_paper_oracle_cost_scalar_bound
-- name    : CountingLLL.ReciprocalTest.paper_oracle_cost_scalar_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:16:43.872197+00:00
-- url     : https://prove2.me/theorems/188e2a50-f38a-4d1b-86bb-2b2842238f23
-- title:
--   Paper oracle-cost expression is strictly below three
-- statement:
--   For $0\le u\le33/80$ and $0\le M\le74/25$, the numerical expression in the paper’s expected oracle-call calculation, with numerator $1-u^2$, is strictly smaller than $3$. This is a scalar inequality; it does not identify the expression with any operational expected cost.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ReciprocalTest.paper_oracle_cost_scalar_bound (u M : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 33/80)
    (hM0 : 0 ≤ M) (hM : M ≤ 74/25) :
    1-u+(1-u^2)/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by sorry
