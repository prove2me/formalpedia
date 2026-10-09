-- Prove2me | Theorems.Thm_CompetingChains_Cournot_retailer_profit_comparison
-- name    : CompetingChains.Cournot.retailer_profit_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:39.822869+00:00
-- url     : https://prove2.me/theorems/646f4ee6-5d9c-4d20-8d3d-cb53773e034d
-- title:
--   §5.3, pp. 20–21 — the retailer weakly gains from sharing iff k ≤ 1/2: Π^{NX_j}_R ≤ Π^{SX_j}_R for k ≤ 1/2, > for k > 1/2
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, and let $\Pi^{X_iX_j}_{R_i,C}$ be retailer $i$'s equilibrium ex-ante profit under Cournot competition when chain $i$ has arrangement $X_i$ and chain $j$ has $X_j$. Then for each $X_j\in\{S,N\}$:
--
--   1. if $k\le 1/2$, then $\Pi^{NX_j}_{R_i,C}\le\Pi^{SX_j}_{R_i,C}$;
--   2. if $k>1/2$, then $\Pi^{NX_j}_{R_i,C}>\Pi^{SX_j}_{R_i,C}$.
--
--   $$
--   k\le\tfrac12\ \Rightarrow\ \Pi^{NX_j}_{R_i,C}\le\Pi^{SX_j}_{R_i,C},\qquad k>\tfrac12\ \Rightarrow\ \Pi^{NX_j}_{R_i,C}>\Pi^{SX_j}_{R_i,C}.
--   $$
--
--   This determines whether the manufacturer must pay the retailer for its signal: no payment for $k\le1/2$, the payment $\Pi^{NX_j}_R-\Pi^{SX_j}_R>0$ for $k>1/2$.
--
--   **Formalization Note** The page states both sentences for both competition types ($Z$); this item is the Cournot case $Z=C$.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), pp. 20–21, §5.3, third and fourth paragraphs

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem retailer_profit_comparison (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    (k ≤ 1 / 2 → ∀ Xj : Arrangement, PiR a c k γ t σsq .N Xj ≤ PiR a c k γ t σsq .S Xj) ∧
    (1 / 2 < k → ∀ Xj : Arrangement, PiR a c k γ t σsq .S Xj < PiR a c k γ t σsq .N Xj) := by sorry

end CompetingChains.Cournot
