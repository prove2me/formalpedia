-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
-- name    : CountingLLL.ContractedWalk.generating_function_recursion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:31:38.895168+00:00
-- url     : https://prove2.me/theorems/0de5c4bd-1431-4b33-898d-1cdb3948a95f
-- title:
--   Contracted walk upward-count generating-function recursion
-- statement:
--   For the absorbed contracted walk from level one, let $G_\theta(z)$ be the generating function of the number of upward steps before absorption. For $0\le\theta<1/3$ and $0\le z\le1$, the source claims $G_\theta(z)=1-\theta+\theta zG_\theta(z)^3$.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.generating_function_recursion (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    generatingFunction θ z = 1-θ+θ*z*(generatingFunction θ z)^3 := by sorry
