-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_11
-- name    : BwSC.LowerBound.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:57.300381+00:00
-- url     : https://prove2.me/theorems/d85d0a49-9d55-459f-8adb-808e512f5d80
-- title:
--   Lemma 11, p. 69 — R^π_{µ^(2)_{j,k}}(T) ≥ R_bad2·P^(2)_{j,k}(E^(2)_{j,k}); averaged over the admissible family Φ₂
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)$, under the standing assumption $q(S,K)+2\le\log_2\log_2(T/K)$ of p. 59 ("we focus on this case in the rest of our proof"). Write $\mathbb P^{(2)}_{j,k}=\mathbb P^\pi_{\mu^{(2)}_{j,k}}$. Then:
--
--   1. for every $j\in[q+2]$, $k\in[K]$: $\ R^\pi_{\mu^{(2)}_{j,k}}(T)\ \ge\ R_{\rm bad2}(S,K,T)\cdot\mathbb P^{(2)}_{j,k}\big(E^{(2)}_{j,k}\big)$;
--   2. every environment of $\Phi_2=\{\mu^{(2)}_{j,k}\}$ is admissible: all mean differences are at most $1$ in absolute value;
--   3. as a result,
--   $$\frac1{|\Phi_2|}\sum_{\mu\in\Phi_2}R^\pi_\mu(T)\ \ge\ R_{\rm bad2}(S,K,T)\cdot\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^{(2)}_{j,k}\big(E^{(2)}_{j,k}\big).$$
--
--   This reduces the second term of Theorem 2 to a lower bound on $\overline{p^{(2)}}$.
--
--   **Formalization Note** The regret is the published `banditRegret`; the average in item 3 runs over the $(q+2)K$ pairs $(j,k)$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 69, Lemma 11 (Reducing regret lower bounds to bad event probability lower bounds)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 11, p. 69: for every `j ∈ [q+2]`, `k ∈ [K]`,
`R^π_{μ^{(2)}_{j,k}}(T) ≥ R_bad2(S,K,T) · P^{(2)}_{j,k}(E^{(2)}_{j,k})`; every `μ^{(2)}_{j,k}` is
admissible; and hence the average regret over `Φ₂` is at least `R_bad2(S,K,T)` times the average
bad-event probability. Under the standing assumption of p. 59. -/
theorem lemma_11 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      Rbad2 S K T *
          ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal ≤
        banditRegret (gaussianBandit (envAlt2 S K T j k)) π T) ∧
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K, ∀ i i' : Fin K,
      |envAlt2 S K T j k i - envAlt2 S K T j k i'| ≤ 1) ∧
    Rbad2 S K T * pbar2 π S T ≤
      1 / (((qIdx S K : ℝ) + 2) * K) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          banditRegret (gaussianBandit (envAlt2 S K T j k)) π T := by sorry

end BwSC.LowerBound
