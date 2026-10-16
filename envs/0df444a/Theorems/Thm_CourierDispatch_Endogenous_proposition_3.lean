-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_proposition_3
-- name    : CourierDispatch.Endogenous.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:49.942981+00:00
-- url     : https://prove2.me/theorems/efc731ac-eac9-49e9-bcf0-f25cde183592
-- title:
--   Proposition 3 — wait-cost threshold and discontinuous switch
-- statement:
--   Fix a radius $r>0$ and $C_B\in[0.58,0.59]$. There is a threshold $c_\infty>0$ such that, for every wait-cost rate $c>0$,
--   $$
--   \operatorname{Opt}_B(C_B,c,r)>\operatorname{Opt}_D(c,r)\iff c<c_\infty,
--   \qquad
--   \operatorname{Opt}_D(c,r)>\operatorname{Opt}_B(C_B,c,r)\iff c>c_\infty.
--   $$
--   As $c$ increases through $c_\infty$, every selection of revenue-maximizing demand has one-sided limits with a strict downward jump; its corresponding limiting price $1-cw$ has one-sided limits with a strict upward jump. An optimal selection exists for every positive $c$.
--
--   This is the paper's crowded-market mode switch driven by customer impatience.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The batch optimization domain is open at zero and both optimal revenues are suprema. At a revenue tie, the selection predicate chooses dedicated delivery; one-sided limits do not depend on that tie convention. The interval for $C_B$ makes the paper's numerical coefficient explicit.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 17, Proposition 3

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem proposition_3 (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) (r : ℝ) (hr : 0 < r) :
    ∃ cinf : ℝ, 0 < cinf ∧
      (∀ c : ℝ, 0 < c →
        (OptD c r < OptB CB c r ↔ c < cinf) ∧
        (OptB CB c r < OptD c r ↔ cinf < c)) ∧
      CostJump CB r cinf := by sorry

end CourierDispatch.Endogenous
