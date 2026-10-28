-- Prove2me | Theorems.Thm_ExpRetail_Monopoly_theorem_1_deriv
-- name    : ExpRetail.Monopoly.theorem_1_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:32.584967+00:00
-- url     : https://prove2.me/theorems/726168eb-29db-46a1-b51f-9bbeb4a13442
-- title:
--   Theorem 1 (∂π∗/∂u^x > 0 at u^x = 0), p. 12 — a free experience of small quality raises the optimal profit
-- statement:
--   Consider the monopoly model of §3.1 under the standing assumptions $t>0$, $\eta>0$, $s>0$, $\lambda>0$. Let $\pi^*(u^x)=\sup_p\pi(p)$ be the retailer's optimal profit (4) when it offers a free experience of quality $u^x$. Then $\pi^*$ is differentiable from the right at $u^x=0$, with a positive derivative:
--   $$\left.\frac{\partial\pi^*}{\partial u^x}\right|_{u^x=0}>0 .$$
--
--   Introducing an experience of small quality therefore increases the retailer's optimal profit above its value at $u^x=0$.
--
--   **Formalization Note** The domain of $u^x$ is $u^x\ge 0$ (Theorem 1: "$\forall u^x\ge0$"), so the derivative is the one-sided derivative within $[0,\infty)$ (`HasDerivWithinAt … (Set.Ici 0) 0`), asserted to exist and to be positive.
-- source:
--   Mutlu, El-Amine & Sahin, Offering memories to sell goods?, SSRN working paper 4617261 (PDF of 2023-10-30), p. 12, Theorem 1 ("∂π∗/∂u^x |_{u^x=0} > 0")

import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_deriv (P : Params) (hP : P.Standing) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (optProfit P) d (Set.Ici 0) 0 := by sorry

end ExpRetail.Monopoly
