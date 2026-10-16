-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_propositions_1_2
-- name    : CourierDispatch.Exogenous.propositions_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:24.408843+00:00
-- url     : https://prove2.me/theorems/51b88f96-c7a3-4df1-a4e6-bec6321fddbf
-- title:
--   Propositions 1 and 2, pp. 13–14 — with exogenous demand, dedicated has the shorter wait exactly when λr is below one threshold
-- statement:
--   Let $C_B\in[0.58,0.59]$. There is a constant $a_1$ with $0<a_1<\tfrac34$ such that for every service radius $r>0$ and every exogenous demand rate $\lambda>0$ with $\lambda r<\tfrac34$ (that is, $\lambda<\mu_D$):
--
--   1. $W_D(\lambda,\mu_D,C_D)<W_B(\lambda,\mu_B,C_B)$ if and only if $\lambda r<a_1$;
--   2. $W_B(\lambda,\mu_B,C_B)<W_D(\lambda,\mu_D,C_D)$ if and only if $\lambda r>a_1$;
--   3. for every inverse valuation c.d.f. $F^{-1}$, every potential-arrival parameter $\Lambda>0$ with $\lambda\le\Lambda r^2$, and every wait-cost rate $c>0$, with
--   $$V(\lambda,w)=\lambda\Big[F^{-1}\Big(1-\frac{\lambda}{\Lambda r^2}\Big)-c\,w\Big],$$
--   the dedicated revenue $V(\lambda,W_D)$ strictly exceeds the batch revenue $V(\lambda,W_B)$ iff $\lambda r<a_1$, and the batch revenue strictly exceeds the dedicated one iff $\lambda r>a_1$.
--
--   Here $\mu_D=\frac3{4r}$, $C_D=\frac98$, $\mu_B=\frac{45\pi}{4r(32+15\pi)}$, and $W_D,W_B$ are the expected waits (5), (12). For $C_B=0.583$ the paper reports $a_1\approx 0.5689$. Proposition 1 is the threshold $\lambda_{ex}=a_1/r$ in the demand rate at fixed radius, and Proposition 2 the threshold $r_{ex}=a_1/\lambda$ in the radius at fixed demand rate.
--
--   **Formalization Note** `lam` is $\lambda$. One constant $a_1$ serves all $r$ and $\lambda$, as in the paper's proof. The range $\lambda r<3/4$ is the stability range of dedicated delivery (batch is then stable as well); beyond it only batch is defined and the paper makes no comparison. The revenue clauses include the model's $0<\Lambda$ and $\lambda\le\Lambda r^2$ from p. 8. $F^{-1}$ is represented by an arbitrary function `Q`; its properties cancel from equal-demand revenue comparisons. $C_B$ ranges over the bracket $[0.58,0.59]$ instead of the paper's numerical value $0.583$.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), pp. 13–14, Propositions 1 and 2; Online Appendix p. 1, proof of Propositions 1 and 2

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Exogenous

/-- Propositions 1 and 2, pp. 13–14, in their common form (Online Appendix p. 1): one constant
`a₁ ∈ (0, 3/4)` such that, for every radius `r > 0` and demand rate `λ > 0` with `λ r < 3/4`,
dedicated has the strictly shorter expected wait (and strictly higher revenue) iff `λ r < a₁`, and
batch does iff `λ r > a₁`. -/
theorem propositions_1_2 (CB : ℝ) (hCB : CBRange CB) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < TD ∧
      ∀ r lam : ℝ, 0 < r → 0 < lam → lam * r < TD →
        (WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam * r < a₁) ∧
        (WB r lam (muB r) CB < WD lam (muD r) CD ↔ a₁ < lam * r) ∧
        (∀ (Q : ℝ → ℝ) (Lam c : ℝ), 0 < Lam → lam ≤ Lam * r ^ 2 → 0 < c →
          (V Q Lam r c lam (WB r lam (muB r) CB) < V Q Lam r c lam (WD lam (muD r) CD) ↔
            lam * r < a₁) ∧
          (V Q Lam r c lam (WD lam (muD r) CD) < V Q Lam r c lam (WB r lam (muB r) CB) ↔
            a₁ < lam * r)) := by sorry

end CourierDispatch.Exogenous
