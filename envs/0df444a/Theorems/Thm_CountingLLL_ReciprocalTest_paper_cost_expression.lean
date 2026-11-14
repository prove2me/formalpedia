-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_paper_cost_expression
-- name    : CountingLLL.ReciprocalTest.paper_cost_expression
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:19:33.966198+00:00
-- url     : https://prove2.me/theorems/a627f7bd-9eda-4d3b-9bb4-a79711f710f7
-- title:
--   Paper oracle-cost expression with the source walk is below three
-- statement:
--   Let $e^{-3/10}\le B\le1$, put $u=2(1-B)/(2-B)$ and $\theta=u^2/(1-u+u^2)$, and let $M$ be the expected reciprocal-counter change weight of the abstract contracted walk from level three and counter two. Then the paper’s displayed expression, with numerator $1-u^2$, is strictly less than three. The equality between that expression and the operational algorithm’s expected oracle calls remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
open CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.paper_cost_expression (B : ℝ) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) (hB1 : B ≤ 1) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let M := (expectedWeightedChanges (ENNReal.ofReal θ) 3 2).toReal
    1-u+(1-u^2)/(1-u+u^2) * (1-u+u/(1-u+u^2)*M) < 3 := by sorry
