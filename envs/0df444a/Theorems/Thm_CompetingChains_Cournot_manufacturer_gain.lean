-- Prove2me | Theorems.Thm_CompetingChains_Cournot_manufacturer_gain
-- name    : CompetingChains.Cournot.manufacturer_gain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:37.869983+00:00
-- url     : https://prove2.me/theorems/0d296185-65bc-4df3-a0b4-024239df40b9
-- title:
--   §5.3, pp. 20–21 — for k ≤ 1/2 free information raises the manufacturer's profit from Π^{NX_j}_M to Π^{SX_j}_M
-- statement:
--   Let $1/3<k\le1/2$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, and let $\Pi^{X_iX_j}_{M_i,C}$ be manufacturer $i$'s equilibrium ex-ante profit under Cournot competition. Then for each $X_j\in\{S,N\}$,
--
--   $$
--   \Pi^{NX_j}_{M_i,C}<\Pi^{SX_j}_{M_i,C}.
--   $$
--
--   When the retailer shares for free, the manufacturer strictly gains, so sharing is a strictly dominant choice for each manufacturer in the stage-one game when $k\le1/2$.
--
--   **Formalization Note** The page states the case $k\le1/2$, and the item keeps that hypothesis. The proof of Proposition 7 (p. 31) prints "$\Pi^{NS}_{M_i,C}>\Pi^{NN}_{M_i,C}$" at this point; those two profits are equal, and the inequality needed there is this one.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), pp. 20–21, §5.3, third paragraph

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem manufacturer_gain (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hk2 : k ≤ 1 / 2) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    ∀ Xj : Arrangement, PiM a c k γ t σsq .N Xj < PiM a c k γ t σsq .S Xj := by sorry

end CompetingChains.Cournot
