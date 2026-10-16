-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_proposition_2
-- name    : CourierDispatch.Exogenous.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:20.137491+00:00
-- url     : https://prove2.me/theorems/792e3efa-7acb-434d-ae7e-bb3c7d3a8a71
-- title:
--   Proposition 2, p. 14 — with exogenous demand, one threshold in the service radius separates dedicated from batch
-- statement:
--   Fix the exogenous demand rate $\lambda>0$ and $C_B\in[0.58,0.59]$. There is a threshold $r_{ex}$ with $0<r_{ex}<\frac3{4\lambda}$ such that for every service radius $r\in\big(0,\frac3{4\lambda}\big)$, with $\mu_D=\frac3{4r}$ and $\mu_B=\frac{45\pi}{4r(32+15\pi)}$:
--
--   1. $W_D(\lambda,\mu_D,C_D)<W_B(\lambda,\mu_B,C_B)$ if and only if $r<r_{ex}$;
--   2. $W_B(\lambda,\mu_B,C_B)<W_D(\lambda,\mu_D,C_D)$ if and only if $r>r_{ex}$;
--   3. for every inverse valuation c.d.f. $F^{-1}$, every potential-arrival parameter $\Lambda>0$ with $\lambda\le\Lambda r^2$, and every wait-cost rate $c>0$, the dedicated revenue strictly exceeds the batch revenue if and only if $r<r_{ex}$, and the batch revenue strictly exceeds the dedicated one if and only if $r>r_{ex}$, with $V(\lambda,w)=\lambda\big[F^{-1}\big(1-\frac{\lambda}{\Lambda r^2}\big)-c\,w\big]$.
--
--   Dedicated delivery is better for small service regions, batch delivery for large ones.
--
--   **Formalization Note** `lam` is $\lambda$. The range $r<3/(4\lambda)$ is $\lambda<\mu_D$, where the dedicated queue is stable; beyond it only batch is defined and the paper makes no comparison. The revenue clauses include the model's $0<\Lambda$ and $\lambda\le\Lambda r^2$ from p. 8. $F^{-1}$ is represented by an arbitrary function `Q`; its properties cancel from equal-demand revenue comparisons. $C_B$ ranges over the bracket $[0.58,0.59]$.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 14, Proposition 2; Online Appendix p. 1, proof of Propositions 1 and 2

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Exogenous

/-- Proposition 2, p. 14: with exogenous demand rate `λ > 0`, there is a threshold
`r_ex ∈ (0, 3/(4λ))` on the service radius, below which dedicated has the strictly shorter expected
wait and strictly higher revenue, and above which batch does. -/
theorem proposition_2 (CB : ℝ) (hCB : CBRange CB) (lam : ℝ) (hlam : 0 < lam) :
    ∃ rEx : ℝ, 0 < rEx ∧ rEx < 3 / (4 * lam) ∧
      ∀ r : ℝ, 0 < r → r < 3 / (4 * lam) →
        (WD lam (muD r) CD < WB r lam (muB r) CB ↔ r < rEx) ∧
        (WB r lam (muB r) CB < WD lam (muD r) CD ↔ rEx < r) ∧
        (∀ (Q : ℝ → ℝ) (Lam c : ℝ), 0 < Lam → lam ≤ Lam * r ^ 2 → 0 < c →
          (V Q Lam r c lam (WB r lam (muB r) CB) < V Q Lam r c lam (WD lam (muD r) CD) ↔
            r < rEx) ∧
          (V Q Lam r c lam (WD lam (muD r) CD) < V Q Lam r c lam (WB r lam (muB r) CB) ↔
            rEx < r)) := by sorry

end CourierDispatch.Exogenous
