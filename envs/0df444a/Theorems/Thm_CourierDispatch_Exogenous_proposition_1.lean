-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_proposition_1
-- name    : CourierDispatch.Exogenous.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:30.701614+00:00
-- url     : https://prove2.me/theorems/291477db-7091-4294-ab6c-a1368ce4fbfa
-- title:
--   Proposition 1, p. 13 — with exogenous demand, one threshold in the demand rate separates dedicated from batch
-- statement:
--   Fix the service radius $r>0$ and $C_B\in[0.58,0.59]$, and suppose the demand rate $\lambda$ is exogenously given. There is a threshold $\lambda_{ex}$ with $0<\lambda_{ex}<\mu_D=\frac3{4r}$ such that for every $\lambda\in(0,\mu_D)$:
--
--   1. $W_D(\lambda,\mu_D,C_D)<W_B(\lambda,\mu_B,C_B)$ if and only if $\lambda<\lambda_{ex}$;
--   2. $W_B(\lambda,\mu_B,C_B)<W_D(\lambda,\mu_D,C_D)$ if and only if $\lambda>\lambda_{ex}$;
--   3. for every inverse valuation c.d.f. $F^{-1}$, every potential-arrival parameter $\Lambda>0$ with $\lambda\le\Lambda r^2$, and every wait-cost rate $c>0$, the dedicated revenue $V(\lambda,W_D)$ strictly exceeds the batch revenue $V(\lambda,W_B)$ if and only if $\lambda<\lambda_{ex}$, and the batch revenue strictly exceeds the dedicated one if and only if $\lambda>\lambda_{ex}$, where
--   $$V(\lambda,w)=\lambda\Big[F^{-1}\Big(1-\frac{\lambda}{\Lambda r^2}\Big)-c\,w\Big].$$
--
--   Dedicated delivery is better at low demand, batch delivery at high demand.
--
--   **Formalization Note** `lam` is $\lambda$. The range $\lambda<\mu_D$ is where the dedicated queue is stable (and then the batch queue is stable too); above $\mu_D$ only batch is defined and the paper makes no comparison. The revenue clauses include the model's $0<\Lambda$ and $\lambda\le\Lambda r^2$ from p. 8. $F^{-1}$ is represented by an arbitrary function `Q`; its properties cancel from equal-demand revenue comparisons. $C_B$ ranges over the bracket $[0.58,0.59]$ instead of the paper's numerical value $0.583$.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 13, Proposition 1; Online Appendix p. 1, proof of Propositions 1 and 2

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Exogenous

/-- Proposition 1, p. 13: with exogenous demand, for every radius `r` there is a threshold
`λ_ex ∈ (0, μ_D)` on the demand rate, below which dedicated has the strictly shorter expected wait
and strictly higher revenue, and above which batch does. -/
theorem proposition_1 (CB : ℝ) (hCB : CBRange CB) (r : ℝ) (hr : 0 < r) :
    ∃ lamEx : ℝ, 0 < lamEx ∧ lamEx < muD r ∧
      ∀ lam : ℝ, 0 < lam → lam < muD r →
        (WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam < lamEx) ∧
        (WB r lam (muB r) CB < WD lam (muD r) CD ↔ lamEx < lam) ∧
        (∀ (Q : ℝ → ℝ) (Lam c : ℝ), 0 < Lam → lam ≤ Lam * r ^ 2 → 0 < c →
          (V Q Lam r c lam (WB r lam (muB r) CB) < V Q Lam r c lam (WD lam (muD r) CD) ↔
            lam < lamEx) ∧
          (V Q Lam r c lam (WD lam (muD r) CD) < V Q Lam r c lam (WB r lam (muB r) CB) ↔
            lamEx < lam)) := by sorry

end CourierDispatch.Exogenous
