-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_lemma_1_part_2
-- name    : DeferredInspection.SingleAgent.lemma_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:17.647695+00:00
-- url     : https://prove2.me/theorems/f9f7f1bf-72a3-46f6-a439-65b7bf9dd2aa
-- title:
--   Lemma 1(2), p. 8 — concavification weakly raises payments
-- statement:
--   For an allocation rule $x:V\to[0,1]$, let $\bar x$ be its pointwise least concave majorant on $V$. Then $\bar x$ is concave and its optimal payment rule weakly dominates that of $x$:
--
--   $$p_x(v)\le p_{\bar x}(v)\qquad(v\in V).$$
--
--   This is the concavification step that reduces the allocation search in (11).
--
--   **Formalization Note** The concave hull is defined as the pointwise infimum of all concave majorants of $x$. For an allocation on $[0,1]$, the family is nonempty and bounded below at each value.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 8, Lemma 1(2); proof p. 29

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem lemma_1_part_2 (x : ℝ → ℝ) (hx : IsAllocation x) :
    ConcaveOn ℝ (Icc 0 1) (concaveHull x) ∧
    ∀ v ∈ Icc (0 : ℝ) 1, optPay x v ≤ optPay (concaveHull x) v := by sorry

end DeferredInspection.SingleAgent
