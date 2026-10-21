-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_claim_lemma_2
-- name    : CapacityRights.Gatekeeper.claim_lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:54.154868+00:00
-- url     : https://prove2.me/theorems/3f90760c-e24c-4217-8bf8-014ec75cc77a
-- title:
--   Claim in proof of Lemma 2: shadow price of fungible capacity
-- statement:
--   Fix a positive total capacity $k$ and a joint shock $\epsilon=(\epsilon_1,\epsilon_2)$ in the support. Let $(q_1^*,q_2^*)$ be any maximizing production pair with $q_i^*\ge0$ and $q_1^*+q_2^*\le k$. The combined contribution-margin value is differentiable at $k$, with derivative equal to the **shadow price of capacity**:
--
--   $$
--   \frac{\partial}{\partial k}CM(k\mid w,\epsilon)=S(k\mid w,\epsilon)
--   =\max\{R'_1(q_1^*,\epsilon_1)-w_1,\;R'_2(q_2^*,\epsilon_2)-w_2\}.
--   $$
--
--   This identifies how much an additional unit of fungible capacity can add to the period contribution margin.
--
--   **Formalization Note** The statement is for $k>0$ and every maximizing pair. The model defines $S$ as the one-sided derivative of the value function on nonnegative capacities; at positive capacity it agrees with the ordinary derivative.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 40 (PDF 43), Claim in proof of Lemma 2

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Claim in the proof of Lemma 2, p. 40 (PDF 43). -/
theorem claim_lemma_2 (E : Env) (hS : E.Standing)
    (k : ℝ) (e : ℝ × ℝ) (q1 q2 : ℝ) (hk : 0 < k)
    (he : e ∈ shockBox E) (hq : IsJointOpt E k e q1 q2) :
    HasDerivAt (fun x => CMtot E x e)
      (max (deriv (fun x => E.R1 x e.1) q1 - E.w1)
           (deriv (fun x => E.R2 x e.2) q2 - E.w2)) k := by sorry

end CapacityRights.Gatekeeper
