-- Prove2me | Theorems.Thm_CompetingChains_Cournot_lemma_2a_fixed_point
-- name    : CompetingChains.Cournot.lemma_2a_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:34.275127+00:00
-- url     : https://prove2.me/theorems/b01a0a50-68f6-48af-b043-18f381649f97
-- title:
--   Proof of Lemma 2(a), p. 28 — the linear strategies with coefficients C^{X_iX_j} solve the best responses (7) and (9)
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$, $\sigma^2>0$, and let $s=t\sigma^2/(1+t\sigma^2)$ be the signal weight, so that $E[\theta\mid Y_i=y]=E[Y_j\mid Y_i=y]=sy$. Let $\bar q=k(a-c)/((\gamma_C+4)k-1)$ and let $C^{X_iX_j}$ be the response coefficients of Lemma 2(a). If chain $j$ plays $q_j=\bar q+C^{X_jX_i}Y_j$, then $E[q_j\mid Y_i=y]=\bar q+C^{X_jX_i}sy$ and $E[q_j]=\bar q$. The claim is that chain $i$'s linear strategy is a best response: for all arrangements $X_i,X_j\in\{S,N\}$ and every signal value $y$,
--
--   $$
--   \bar q+C^{X_iX_j}y=\hat q^{X_i}\big(m=sy,\ e=\bar q+C^{X_jX_i}sy,\ E=\bar q\big),
--   $$
--
--   where $\hat q^S$ is the best response (7) and $\hat q^N$ the best response (9).
--
--   This is the existence half of Lemma 2(a) for the quantities: the pair of linear strategies is a Bayesian equilibrium of the quantity stage. The coefficients $C^{X_iX_j}$ are the inputs of every profit formula of the mission.
--
--   **Formalization Note** The conditional expectations are substituted by their values under the linear information structure (p. 8), so the statement is an identity between closed forms. The page cites only (7); for $X_i=N$ the relevant best response is (9), which is what is stated. Uniqueness, delegated by the paper to Ha et al. (2011), is not stated; the wholesale price and cost reduction lines of Lemma 2(a) are not stated.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 28, proof of Lemma 2(a); Lemma 2(a) p. 15; (7) and (9) p. 14; information structure p. 8

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem lemma_2a_fixed_point (a c k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ht : 0 < t) (hσ : 0 < σsq) :
    ∀ (Xi Xj : Arrangement) (y : ℝ),
      qbar a c k γ + C k γ t σsq Xi Xj * y =
        br a c k γ Xi (sig t σsq * y)
          (qbar a c k γ + C k γ t σsq Xj Xi * (sig t σsq * y)) (qbar a c k γ) := by sorry

end CompetingChains.Cournot
