-- Prove2me | Theorems.Thm_CompetingChains_Cournot_proposition_6a_VN_iff_h
-- name    : CompetingChains.Cournot.proposition_6a_VN_iff_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:27:42.149806+00:00
-- url     : https://prove2.me/theorems/f8807976-c592-481d-af04-14decc6fd035
-- title:
--   Proof of Proposition 6(a), p. 30 — V^N_{i,C} > 0 if and only if h > 0
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, and let $V^N_{i,C}=\Pi^{SN}_{i,C}-\Pi^{NN}_{i,C}$ be the value of information sharing to chain $i$ when the rival chain does not share. Then $V^N_{i,C}>0$ if and only if $h>0$, where
--
--   $$
--   h=k(4k-1)\frac{t^4\sigma^8\gamma_C^4}{(t\sigma^2+1)^4}-16k^2\frac{t^2\sigma^4\gamma_C^2}{(t\sigma^2+1)^2}-8(-6k+4k^2+1).
--   $$
--
--   As a quadratic in $\rho=t^2\sigma^4\gamma_C^2/(t\sigma^2+1)^2$, $h$ determines the threshold $k^N_C$ of Proposition 6(a).
--
--   **Formalization Note** $h$ is written as printed, in $t$, $\sigma^2$ and $\gamma_C$.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 30, proof of Proposition 6, part (a), first display

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem proposition_6a_VN_iff_h (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    0 < V a c k γ t σsq .N ↔
      0 < k * (4 * k - 1) * (t ^ 4 * σsq ^ 4 * γ ^ 4 / (t * σsq + 1) ^ 4) -
        16 * k ^ 2 * (t ^ 2 * σsq ^ 2 * γ ^ 2 / (t * σsq + 1) ^ 2) -
        8 * (-6 * k + 4 * k ^ 2 + 1) := by sorry

end CompetingChains.Cournot
