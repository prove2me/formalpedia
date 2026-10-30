-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_9
-- name    : BwSC.LowerBound.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:56.313754+00:00
-- url     : https://prove2.me/theorems/bdb55d08-e1db-4dd6-afbe-ad659223ea46
-- title:
--   Lemma 9, p. 68 — R^π_{µ^(1)_{j,k}}(T) ≥ R_bad·P^(1)_{j,k}(E^(1)_{j,k}); averaged over the admissible family Φ₁ (q ≥ 1)
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)\ge1$, under the standing assumption $q(S,K)+2\le\log_2\log_2(T/K)$ of p. 59 ("we focus on this case in the rest of our proof"). Write $\mathbb P^{(1)}_{j,k}=\mathbb P^\pi_{\mu^{(1)}_{j,k}}$ and $R^\pi_\mu(T)=T\mu^*-\mathbb E^\pi_\mu[\sum_{t=1}^TX_t]$. Then:
--
--   1. for every $j\in[q+2]$, $k\in[K]$: $\ R^\pi_{\mu^{(1)}_{j,k}}(T)\ \ge\ R_{\rm bad}(S,K,T)\cdot\mathbb P^{(1)}_{j,k}\big(E^{(1)}_{j,k}\big)$;
--   2. every environment of $\Phi_1=\{\mu^{(1)}_{j,k}\}$ is admissible: $|\mu^{(1)}_{j,k;i}-\mu^{(1)}_{j,k;i'}|\le1$ for all arms $i,i'$;
--   3. as a result,
--   $$\frac1{|\Phi_1|}\sum_{\mu\in\Phi_1}R^\pi_\mu(T)\ \ge\ R_{\rm bad}(S,K,T)\cdot\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^{(1)}_{j,k}\big(E^{(1)}_{j,k}\big).$$
--
--   Since the worst-case regret over admissible environments is at least the average over $\Phi_1$, this reduces the first term of Theorem 2 to a lower bound on the average bad-event probability $\overline{p^{(1)}}$.
--
--   **Formalization Note** The regret is the published `banditRegret` of the Gaussian environment. The average in item 3 runs over the $(q+2)K$ pairs $(j,k)$, as on the page. The page's "$R^\pi(T)\ge\frac1{|\Phi_1|}\sum$" step is represented by the admissibility in item 2. The hypotheses $q\ge1$ and the standing assumption are those of Lemma 8.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 68, Lemma 9 (Reducing regret lower bounds to bad event probability lower bounds); Φ₁ p. 65

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 9, p. 68: for every `j ∈ [q+2]`, `k ∈ [K]`,
`R^π_{μ^{(1)}_{j,k}}(T) ≥ R_bad(S,K,T) · P^{(1)}_{j,k}(E^{(1)}_{j,k})`; every `μ^{(1)}_{j,k}` is an
admissible instance (mean spread at most `1`); and hence the average regret over `Φ₁` is at least
`R_bad(S,K,T)` times the average bad-event probability. Stated for `q(S,K) ≥ 1` under the
standing assumption of p. 59. -/
theorem lemma_9 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      Rbad S K T *
          ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal ≤
        banditRegret (gaussianBandit (envAlt1 S K T j k)) π T) ∧
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K, ∀ i i' : Fin K,
      |envAlt1 S K T j k i - envAlt1 S K T j k i'| ≤ 1) ∧
    Rbad S K T * pbar1 π S T ≤
      1 / (((qIdx S K : ℝ) + 2) * K) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          banditRegret (gaussianBandit (envAlt1 S K T j k)) π T := by sorry

end BwSC.LowerBound
