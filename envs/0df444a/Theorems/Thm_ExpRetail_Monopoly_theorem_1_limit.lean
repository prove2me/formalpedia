-- Prove2me | Theorems.Thm_ExpRetail_Monopoly_theorem_1_limit
-- name    : ExpRetail.Monopoly.theorem_1_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:32.873868+00:00
-- url     : https://prove2.me/theorems/85dcfe84-2894-4179-8ffa-d786851a436b
-- title:
--   Theorem 1 (lim π∗ = −∞ < π∗N > 0), p. 12 — high-quality free experiences drive the optimal profit to −∞
-- statement:
--   Consider the monopoly model of §3.1 under the standing assumptions $t>0$, $\eta>0$, $s>0$, $\lambda>0$. Let $\pi^*(u^x)=\sup_p\pi(p)$ be the optimal profit (4) with a free experience of quality $u^x$, and $\pi^{*N}=\sup_p\pi^N(p)$ the optimal profit (5) without one. Then
--   $$\lim_{u^x\to\infty}\pi^*(u^x)=-\infty\qquad\text{and}\qquad\pi^{*N}>0 .$$
--
--   A free experience of high enough quality makes the retailer strictly worse off than offering none: its cost $\eta(u^x)^2$, borne also by free riders, outgrows every gain in sales.
--
--   **Formalization Note** The paper's chain "$\lim_{u^x\to\infty}\pi^*=-\infty<\pi^{*N}>0$" is read as the two facts above; "$-\infty<\pi^{*N}$" holds automatically for a real number.
-- source:
--   Mutlu, El-Amine & Sahin, Offering memories to sell goods?, SSRN working paper 4617261 (PDF of 2023-10-30), p. 12, Theorem 1 ("lim_{u^x→∞} π∗ = −∞ < π∗N > 0")

import Mathlib
import Definitions.Def_ExpRetail_Monopoly_Model

namespace ExpRetail.Monopoly

theorem theorem_1_limit (P : Params) (hP : P.Standing) :
    Filter.Tendsto (optProfit P) Filter.atTop Filter.atBot ∧ 0 < optProfitN P := by sorry

end ExpRetail.Monopoly
