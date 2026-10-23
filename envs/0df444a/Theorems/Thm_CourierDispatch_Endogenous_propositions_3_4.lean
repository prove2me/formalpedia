-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_propositions_3_4
-- name    : CourierDispatch.Endogenous.propositions_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:05.732984+00:00
-- url     : https://prove2.me/theorems/1fde3149-e9e5-49c8-bd3f-f390ebd0781b
-- title:
--   Propositions 3 and 4 — one crowded-market threshold in $cr$
-- statement:
--   Fix the paper's batch variation coefficient $C_B$ in $[0.58,0.59]$. There is one constant $\alpha^*>0$ such that, for all wait costs $c>0$ and radii $r>0$,
--   $$
--   \operatorname{Opt}_B(C_B,c,r)>\operatorname{Opt}_D(c,r)\iff cr<\alpha^*,
--   \qquad
--   \operatorname{Opt}_D(c,r)>\operatorname{Opt}_B(C_B,c,r)\iff cr>\alpha^*.
--   $$
--   At fixed $r$, the switch occurs at $c_\infty=\alpha^*/r$; at fixed $c$, it occurs at $r_\infty=\alpha^*/c$. At either switch, every selection of optimal demand has a strict downward jump and its induced limiting price a strict upward jump, with both one-sided limits existing. Optimal selections exist at all positive parameters. The paper reports $\alpha^*\approx0.1355$ at $C_B=0.583$.
--
--   The theorem combines Propositions 3 and 4 through the dimensionless product $cr$.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The optimal revenues are suprema of the paper's closed-form limiting revenue over the stable demand domains; no answer is built into their definitions. Batch demand zero and the service-rate poles are excluded. At equal revenues, dedicated is selected, without affecting one-sided limits. The bracket for $C_B$ is a disclosed strengthening of the paper's numerical substitution.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 17, Propositions 3 and 4; Online Appendix p. 3, (A.7)–(A.8)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem propositions_3_4 (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) :
    ∃ αs : ℝ, 0 < αs ∧
      (∀ c r : ℝ, 0 < c → 0 < r →
        (OptD c r < OptB CB c r ↔ c * r < αs) ∧
        (OptB CB c r < OptD c r ↔ αs < c * r)) ∧
      (∀ r : ℝ, 0 < r → CostJump CB r (αs / r)) ∧
      (∀ c : ℝ, 0 < c → RadiusJump CB c (αs / c)) := by sorry

end CourierDispatch.Endogenous
