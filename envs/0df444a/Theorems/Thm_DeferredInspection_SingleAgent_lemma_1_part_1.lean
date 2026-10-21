-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_lemma_1_part_1
-- name    : DeferredInspection.SingleAgent.lemma_1_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:12.427826+00:00
-- url     : https://prove2.me/theorems/a047dd79-c01d-4a7d-93d4-2a8dad2e7201
-- title:
--   Lemma 1(1), p. 8 — improving an allocation at a decrease or endpoint
-- statement:
--   Let $x:V\to[0,1]$ be an allocation rule and $p_x$ its optimal payment. If $v_1<v_2$ but $x(v_2)<x(v_1)$, replacing $x(v_2)$ by $x(v_1)$ weakly raises $p_x(v)$ at every $v\in V$. Replacing $x(0)$ by zero weakly raises payments at every positive value. Replacing $x(1)$ by one weakly raises payments at every value:
--
--   $$p_x(v)\le p_{\widetilde x}(v)$$
--
--   for each of these changes and the stated value range.
--
--   These improvement operations explain the monotonicity and endpoint conditions used to search for an optimum.
--
--   **Formalization Note** The paper phrases these as properties of every optimal allocation; pointwise changes on null sets prevent that literal conclusion. The formal statement captures the payment comparisons from pp. 8 and 28–29.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 8, Lemma 1(1); proof pp. 28–29

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem lemma_1_part_1 (x : ℝ → ℝ) (hx : IsAllocation x) :
    (∀ v1 v2, 0 ≤ v1 → v1 < v2 → v2 ≤ 1 → x v2 < x v1 →
      ∀ v ∈ Icc (0 : ℝ) 1, optPay x v ≤ optPay (Function.update x v2 (x v1)) v) ∧
    (∀ v ∈ Ioc (0 : ℝ) 1, optPay x v ≤ optPay (Function.update x 0 0) v) ∧
    (∀ v ∈ Icc (0 : ℝ) 1, optPay x v ≤ optPay (Function.update x 1 1) v) := by sorry

end DeferredInspection.SingleAgent
