-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_lemma_1
-- name    : AdvSellUpgrade.Online.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:31.99548+00:00
-- url     : https://prove2.me/theorems/6bb3e8c9-7d4d-43dd-af4b-d00aaf0248a4
-- title:
--   Lemma 1, p. 14 — the spot-only equilibrium cutoffs (cₕᵉ, cₗᵉ) are given by (5)
-- statement:
--   Assume $0<\lambda_l<\lambda_h<\mu$ and $\bar c>0$. All customers buy on the spot, at the regular price $B_s$ or the fast-track price $P_s\ge B_s$; write $d=P_s-B_s\ge0$. For a rate $\lambda$ let $W_F(c)=\lambda/(\mu(\mu-(1-c/\bar c)\lambda))$ and $W_R(c)=\mu W_F(c)/(\mu-\lambda)$. Call $c$ an **equilibrium cutoff** at rate $\lambda$ if either
--   1. $0\le c<\bar c$ and $d=c\,\bigl(W_R(c)-W_F(c)\bigr)$, or
--   2. $c=\bar c$ and $\bar c\,\bigl(W_R(\bar c)-W_F(\bar c)\bigr)\le d$.
--
--   Then $(c_h,c_l)$ is a pair of equilibrium cutoffs at the rates $\lambda_h$ and $\lambda_l$ if and only if
--   $$(c_h,c_l)=\begin{cases}\Bigl(\dfrac{d\mu(\mu-\lambda_h)^2\bar c}{\lambda_h^2\bar c-d\mu(\mu-\lambda_h)\lambda_h},\ \dfrac{d\mu(\mu-\lambda_l)^2\bar c}{\lambda_l^2\bar c-d\mu(\mu-\lambda_l)\lambda_l}\Bigr), & 0\le d<\dfrac{\lambda_l^2\bar c}{\mu^2(\mu-\lambda_l)},\\[3mm] \Bigl(\dfrac{d\mu(\mu-\lambda_h)^2\bar c}{\lambda_h^2\bar c-d\mu(\mu-\lambda_h)\lambda_h},\ \bar c\Bigr), & \dfrac{\lambda_l^2\bar c}{\mu^2(\mu-\lambda_l)}\le d<\dfrac{\lambda_h^2\bar c}{\mu^2(\mu-\lambda_h)},\\[3mm] (\bar c,\bar c), & d\ge\dfrac{\lambda_h^2\bar c}{\mu^2(\mu-\lambda_h)}.\end{cases}$$
--
--   So the equilibrium is unique and given in closed form: a low fast-track price gives two interior cutoffs, a medium one an interior cutoff on crowded days only, and a high one no fast-track purchase at all. It is the price form of the spot-only problem solved in Proposition 3.
--
--   **Formalization Note** The equilibrium notion is the paper's Definition 1 restricted to cutoff strategies, in the two cases of the proof of Lemma 1 (Online Appendix p. 5): an interior cutoff where the marginal customer is indifferent, or the corner $c=\bar c$ where the customer with the highest cost weakly prefers regular. Two readings are disclosed: (i) at $d=0$ the cutoff $0$ is allowed, as in the printed range $0\le P_s-B_s$ of (5) (Proposition 2 elsewhere claims a positive cutoff); (ii) at $d=\bar c\,(W_R(\bar c)-W_F(\bar c))$ the top customer is indifferent and the corner case is taken, since a single indifferent customer does not change the cutoff. The parameter $\alpha$ plays no role here; the statement is made under the mission's standing assumptions.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 14, Lemma 1, (5); Online Appendix p. 5, proof of Lemma 1, (D.2)

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Lemma 1, p. 14: with all customers offline and prices `(Bs, Ps)`, `Ps ≥ Bs`, the pair
`(ch, cl)` of equilibrium cutoffs in the two states is exactly the pair given by (5). -/
theorem lemma_1 (P : Params) (hP : P.Standing) (Ps ch cl : ℝ) (hPs : P.Bs ≤ Ps) :
    (IsSpotEqCutoff P.mu P.cbar P.lamH (Ps - P.Bs) ch ∧
        IsSpotEqCutoff P.mu P.cbar P.lamL (Ps - P.Bs) cl) ↔
      (ch, cl) =
        (if Ps - P.Bs < P.lamL ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamL)) then
          ((Ps - P.Bs) * P.mu * (P.mu - P.lamH) ^ 2 * P.cbar /
              (P.lamH ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamH) * P.lamH),
            (Ps - P.Bs) * P.mu * (P.mu - P.lamL) ^ 2 * P.cbar /
              (P.lamL ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamL) * P.lamL))
        else if Ps - P.Bs < P.lamH ^ 2 * P.cbar / (P.mu ^ 2 * (P.mu - P.lamH)) then
          ((Ps - P.Bs) * P.mu * (P.mu - P.lamH) ^ 2 * P.cbar /
              (P.lamH ^ 2 * P.cbar - (Ps - P.Bs) * P.mu * (P.mu - P.lamH) * P.lamH),
            P.cbar)
        else (P.cbar, P.cbar)) := by sorry

end AdvSellUpgrade.Online
