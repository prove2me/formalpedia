-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_proposition_4
-- name    : CourierDispatch.Endogenous.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:57.559977+00:00
-- url     : https://prove2.me/theorems/7037b854-0501-4a32-bcba-457c8fc3c841
-- title:
--   Proposition 4 — radius threshold and discontinuous switch
-- statement:
--   Fix a wait-cost rate $c>0$ and $C_B\in[0.58,0.59]$. There is a threshold $r_\infty>0$ such that, for every service radius $r>0$,
--   $$
--   \operatorname{Opt}_B(C_B,c,r)>\operatorname{Opt}_D(c,r)\iff r<r_\infty,
--   \qquad
--   \operatorname{Opt}_D(c,r)>\operatorname{Opt}_B(C_B,c,r)\iff r>r_\infty.
--   $$
--   As $r$ increases through $r_\infty$, every selection of revenue-maximizing demand has one-sided limits with a strict downward jump; the corresponding limiting price has one-sided limits with a strict upward jump. An optimal selection exists for every positive $r$.
--
--   This is the same crowded-market mode switch viewed as the service region expands.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The batch domain excludes zero, where its wait is singular. The two optimum values are suprema, and a tie is assigned to dedicated delivery only to make the optimal-selection predicate total. The bracket for $C_B$ makes the numerical coefficient explicit.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 17, Proposition 4

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem proposition_4 (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (c : ℝ) (hc : 0 < c) :
    ∃ rinf : ℝ, 0 < rinf ∧
      (∀ r : ℝ, 0 < r →
        (OptD c r < OptB CB c r ↔ r < rinf) ∧
        (OptB CB c r < OptD c r ↔ rinf < r)) ∧
      RadiusJump CB c rinf := by sorry

end CourierDispatch.Endogenous
