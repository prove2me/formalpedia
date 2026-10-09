-- Prove2me | Theorems.Thm_CompetingChains_Cournot_proposition_6a_VS_iff_g
-- name    : CompetingChains.Cournot.proposition_6a_VS_iff_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:30.228507+00:00
-- url     : https://prove2.me/theorems/8fb23fb9-cd50-476c-8eea-3d8e3b08d3b5
-- title:
--   Proof of Proposition 6(a), p. 29 — V^S_{i,C} > 0 if and only if g > 0
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, and let $V^S_{i,C}=\Pi^{SS}_{i,C}-\Pi^{NS}_{i,C}$ be the value of information sharing to chain $i$ when the rival chain shares. Then $V^S_{i,C}>0$ if and only if $g>0$, where
--
--   $$
--   g=k^3\frac{t^4\sigma^8\gamma_C^4}{(t\sigma^2+1)^4}-8k^3\frac{t^2\sigma^4\gamma_C^2}{(t\sigma^2+1)^2}-2(4k-1)(-6k+4k^2+1).
--   $$
--
--   With $\xi=t^2\sigma^4\gamma_C^2/(t\sigma^2+1)^2$, $g$ is a quadratic in $\xi$; the threshold $k^S_C$ of Proposition 6(a) is read off from its roots.
--
--   **Formalization Note** $g$ is written as printed, in $t$, $\sigma^2$ and $\gamma_C$ ($\sigma^8=(\sigma^2)^4$, $\sigma^4=(\sigma^2)^2$).
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 29, proof of Proposition 6, part (a), first display

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem proposition_6a_VS_iff_g (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    0 < V a c k γ t σsq .S ↔
      0 < k ^ 3 * (t ^ 4 * σsq ^ 4 * γ ^ 4 / (t * σsq + 1) ^ 4) -
        8 * k ^ 3 * (t ^ 2 * σsq ^ 2 * γ ^ 2 / (t * σsq + 1) ^ 2) -
        2 * (4 * k - 1) * (-6 * k + 4 * k ^ 2 + 1) := by sorry

end CompetingChains.Cournot
