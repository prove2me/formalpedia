-- Prove2me | Theorems.Thm_CompetingChains_Cournot_lemma_3_coeff_differences_3_4
-- name    : CompetingChains.Cournot.lemma_3_coeff_differences_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:39.233706+00:00
-- url     : https://prove2.me/theorems/b7b8cce3-6f61-45d7-9503-966aebf67ccc
-- title:
--   Proof of Lemma 3, displays (3)–(4), p. 28 — C^{SS} − C^{SN} and C^{NS} − C^{NN} in closed form, positive iff k > 1/2
-- statement:
--   Let $k>1/3$, $0<\gamma_C<1$, $t>0$, $\sigma^2>0$, write $\tau=t\sigma^2$, and let $C^{X_jX_i}$ be the response coefficient of chain $j$ (arrangement $X_j$ first) from Lemma 2(a). Then
--
--   $$
--   \begin{aligned}
--   C^{SS}-C^{SN}&=\frac{k\tau^2\gamma_C(\tau+1)(2k-1)}{\big((4\tau+4+\gamma_C\tau)k-(\tau+1)\big)\big((8(1+\tau)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2\big)},\\
--   C^{NS}-C^{NN}&=\frac{\tau^2\gamma_C(\tau+1)(2k-1)}{(2\tau+\tau\gamma_C+2)\big((8(1+\tau)^2-\gamma_C^2\tau^2)k-2(\tau+1)^2\big)},
--   \end{aligned}
--   $$
--
--   and each of the two differences is positive if and only if $k>1/2$.
--
--   These are the effects of sharing in chain $i$ on the responsiveness of the rival's quantity (Lemma 3(b)).
--
--   **Formalization Note** The hypothesis $\gamma_C>0$ is added: at $\gamma_C=0$ both differences vanish and the "if and only if" fails for $k>1/2$.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 28, proof of Lemma 3, displays (3) and (4)

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem lemma_3_coeff_differences_3_4 (k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (ht : 0 < t) (hσ : 0 < σsq) :
    (C k γ t σsq .S .S - C k γ t σsq .S .N =
        k * (t * σsq) ^ 2 * γ * (t * σsq + 1) * (2 * k - 1) /
          (((4 * (t * σsq) + 4 + γ * (t * σsq)) * k - (t * σsq + 1)) *
            ((8 * (1 + t * σsq) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)) ∧
      (0 < C k γ t σsq .S .S - C k γ t σsq .S .N ↔ 1 / 2 < k)) ∧
    (C k γ t σsq .N .S - C k γ t σsq .N .N =
        (t * σsq) ^ 2 * γ * (t * σsq + 1) * (2 * k - 1) /
          ((2 * (t * σsq) + t * σsq * γ + 2) *
            ((8 * (1 + t * σsq) ^ 2 - γ ^ 2 * (t * σsq) ^ 2) * k - 2 * (t * σsq + 1) ^ 2)) ∧
      (0 < C k γ t σsq .N .S - C k γ t σsq .N .N ↔ 1 / 2 < k)) := by sorry

end CompetingChains.Cournot
