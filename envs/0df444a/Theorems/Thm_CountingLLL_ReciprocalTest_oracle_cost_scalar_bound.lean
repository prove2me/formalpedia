-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_oracle_cost_scalar_bound
-- name    : CountingLLL.ReciprocalTest.oracle_cost_scalar_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:12:38.716183+00:00
-- url     : https://prove2.me/theorems/9aed4f7e-8425-489a-b0f9-5b91ed003d78
-- title:
--   ReciprocalTest source oracle-cost expression is below three
-- statement:
--   For $0\le u\le33/80$ and $0\le M\le74/25$, the displayed formal expression with numerator $(1-u)^2$ is strictly less than $3$. This is a valid auxiliary inequality but is not the paper’s oracle-cost expression: the source uses $1-u^2$ instead. The source-faithful correction is being formalized separately.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib

theorem CountingLLL.ReciprocalTest.oracle_cost_scalar_bound (u M : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 33/80)
    (hM0 : 0 ≤ M) (hM : M ≤ 74/25) :
    1-u+(1-u)^2/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by sorry
