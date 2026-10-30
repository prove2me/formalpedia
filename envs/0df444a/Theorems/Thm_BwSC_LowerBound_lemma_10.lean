-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_10
-- name    : BwSC.LowerBound.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:51.347616+00:00
-- url     : https://prove2.me/theorems/7192fc0b-af4a-4587-ac14-b5925ba336bf
-- title:
--   Lemma 10, p. 69 — under µ^(2)_{j,k}, E[(Tµ* − Σ_t µ_{a_t})·1{E^(2)_{j,k}}] ≥ R_bad2(S,K,T)·P(E^(2)_{j,k})
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)$, under the standing assumption $q(S,K)+2\le\log_2\log_2(T/K)$ of p. 59 ("we focus on this case in the rest of our proof"). For every $j\in[q+2]$, $k\in[K]$, under the alternative environment $\mu^{(2)}_{j,k}$ (mean $\Delta^{(2)}_j$ on arm $k$, $0$ elsewhere), with $\mathbb P=\mathbb P^\pi_{\mu^{(2)}_{j,k}}$ and $\mu^*=\max_i\mu^{(2)}_{j,k;i}$,
--   $$\mathbb E\Big[\Big(T\mu^*-\sum_{t=1}^T\mu^{(2)}_{j,k;a_t}\Big)\mathbb 1\big\{E^{(2)}_{j,k}\big\}\Big]\ \ge\ R_{\rm bad2}(S,K,T)\cdot\mathbb P\big(E^{(2)}_{j,k}\big),\qquad R_{\rm bad2}(S,K,T)=\frac{K}{4(q+2)}\Big(\frac TK\Big)^{\frac1{2-2^{-q-1}}}.$$
--
--   This is the bad-event step for the second term of Theorem 2.
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. Here every $\Delta^{(2)}_j\ge0$, so $\mu^*=\mu^{(2)}_{j,k;k}$ and the integrand is the page's. The conditional expectation is stated in product form. The page gives no separate proof ("similar to Appendix J.3.1").
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 69, Lemma 10 (From risky events to bad events); gaps p. 68, environments p. 69

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 10, p. 69 (product form of the conditional expectation): under the alternative
environment `μ^{(2)}_{j,k}`,
`E[(Tμ* - Σ_t μ_{a_t}) · 1{E^{(2)}_{j,k}}] ≥ R_bad2(S,K,T) · P(E^{(2)}_{j,k})`, under the standing
assumption `q(S,K) + 2 ≤ log₂ log₂ (T/K)` of p. 59. -/
theorem lemma_10 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)))
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    Rbad2 S K T *
        ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal ≤
      ∫ h in E2 S K T j k, regretOf (envAlt2 S K T j k) h
        ∂(banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) := by sorry

end BwSC.LowerBound
