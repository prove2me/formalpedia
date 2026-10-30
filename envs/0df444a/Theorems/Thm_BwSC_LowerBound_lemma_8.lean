-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_8
-- name    : BwSC.LowerBound.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:51.764993+00:00
-- url     : https://prove2.me/theorems/2148b2be-3fea-48b9-8b3f-b649328bc3a6
-- title:
--   Lemma 8, p. 66 — under µ^(1)_{j,k}, E[(Tµ* − Σ_t µ_{a_t})·1{E^(1)_{j,k}}] ≥ R_bad(S,K,T)·P(E^(1)_{j,k}) (q ≥ 1, regret integrand)
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, write $q=q(S,K)$, $r=r(S,K)$, and assume $q\ge1$ and the standing assumption $q(S,K)+2\le\log_2\log_2(T/K)$ of p. 59 ("we focus on this case in the rest of our proof"). For every $j\in[q+2]$ and $k\in[K]$, under the alternative environment $\mu^{(1)}_{j,k}$ (mean $\Delta^{(1)}_j$ on arm $k$, $0$ elsewhere), with $\mathbb P=\mathbb P^\pi_{\mu^{(1)}_{j,k}}$ and $\mu^*=\max_i\mu^{(1)}_{j,k;i}$,
--   $$\mathbb E\Big[\Big(T\mu^*-\sum_{t=1}^T\mu^{(1)}_{j,k;a_t}\Big)\mathbb 1\big\{E^{(1)}_{j,k}\big\}\Big]\ \ge\ R_{\rm bad}(S,K,T)\cdot\mathbb P\big(E^{(1)}_{j,k}\big),\qquad R_{\rm bad}(S,K,T)=\frac{K-r}{8(q+2)}\Big(\frac{T}{K-r}\Big)^{\frac1{2-2^{-q}}}.$$
--   When $\mathbb P(E^{(1)}_{j,k})>0$ this says that the regret conditional on the risky event is at least $R_{\rm bad}(S,K,T)$: under $\mu^{(1)}_{j,k}$ the risky event is a bad event.
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. (i) The page's integrand is $T\mu^{(1)}_{j,k;k}-\sum_t\mu^{(1)}_{j,k;a_t}$. For $j=q+2$, $\mu^{(1)}_{j,k;k}=\Delta^{(1)}_{q+2}<0$ is not the optimal mean and that integrand is $\le0$, so the printed statement fails there; the proof (pp. 66–67) bounds the regret $T\mu^*-\sum_t\mu_{a_t}$, which is stated here. For $j\le q+1$ the two integrands coincide. (ii) The conditional expectation is stated in product form, which is what Lemma 9 uses. (iii) $q\ge1$ is assumed because for $q=0$ the gap $\Delta^{(1)}_{q+2}$ divides by $t^{(1)}_0=0$ and the page's construction is undefined.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 66, Lemma 8 (From risky events to bad events), proof pp. 66–67; gaps and environments p. 65

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 8, p. 66 (integrand = the regret `Tμ* - Σ_t μ_{a_t}`; product form of the conditional
expectation): under the alternative environment `μ^{(1)}_{j,k}`,
`E[(Tμ* - Σ_t μ_{a_t}) · 1{E^{(1)}_{j,k}}] ≥ R_bad(S,K,T) · P(E^{(1)}_{j,k})`. Stated for
`q(S,K) ≥ 1` under the standing assumption `q(S,K) + 2 ≤ log₂ log₂ (T/K)` of p. 59. -/
theorem lemma_8 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)))
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    Rbad S K T *
        ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal ≤
      ∫ h in E1 S K T j k, regretOf (envAlt1 S K T j k) h
        ∂(banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) := by sorry

end BwSC.LowerBound
