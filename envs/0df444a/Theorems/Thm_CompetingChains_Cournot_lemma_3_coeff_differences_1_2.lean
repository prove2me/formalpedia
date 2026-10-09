-- Prove2me | Theorems.Thm_CompetingChains_Cournot_lemma_3_coeff_differences_1_2
-- name    : CompetingChains.Cournot.lemma_3_coeff_differences_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:33.893978+00:00
-- url     : https://prove2.me/theorems/9ecedf13-bdb6-40c4-8fbc-082b9cb3163c
-- title:
--   Proof of Lemma 3, displays (1)–(2), p. 28 — C^{SS} − C^{NS} and C^{SN} − C^{NN} in closed form, positive iff k < 1/2
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, write $\tau=t\sigma^2$, and let $C^{X_iX_j}$ be the response coefficients of Lemma 2(a). Then
--
--   $$
--   \begin{aligned}
--   C^{SS}-C^{NS}&=\frac{\tau(\tau+1)^2(4k-1)(1-2k)}{\big((4\tau+4+\gamma_C\tau)k-(\tau+1)\big)\big((8(\tau+1)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2\big)},\\
--   C^{SN}-C^{NN}&=\frac{2\tau(\tau+1)^2(1-2k)}{(2\tau+\tau\gamma_C+2)\big((8(1+\tau)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2\big)},
--   \end{aligned}
--   $$
--
--   and each of the two differences is positive if and only if $k<1/2$.
--
--   These are the effects of sharing in chain $i$ on the responsiveness of chain $i$'s own quantity (Lemma 3(b)).
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 28, proof of Lemma 3, displays (1) and (2)

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem lemma_3_coeff_differences_1_2 (k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    (C k γ t σsq .S .S - C k γ t σsq .N .S =
        t * σsq * (t * σsq + 1) ^ 2 * (4 * k - 1) * (1 - 2 * k) /
          (((4 * (t * σsq) + 4 + γ * (t * σsq)) * k - (t * σsq + 1)) *
            ((8 * (t * σsq + 1) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)) ∧
      (0 < C k γ t σsq .S .S - C k γ t σsq .N .S ↔ k < 1 / 2)) ∧
    (C k γ t σsq .S .N - C k γ t σsq .N .N =
        2 * (t * σsq) * (t * σsq + 1) ^ 2 * (1 - 2 * k) /
          ((2 * (t * σsq) + t * σsq * γ + 2) *
            ((8 * (1 + t * σsq) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)) ∧
      (0 < C k γ t σsq .S .N - C k γ t σsq .N .N ↔ k < 1 / 2)) := by sorry

end CompetingChains.Cournot
