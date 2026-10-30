-- Prove2me | Theorems.Thm_BwSC_LowerBound_corollary_4
-- name    : BwSC.LowerBound.corollary_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:01.167048+00:00
-- url     : https://prove2.me/theorems/522dc7b3-2715-4489-b059-615c2a598214
-- title:
--   Corollary 4, pp. 61–62 — average first-class risky-event probability ≥ (K−r)/(2(q+2)²K), second-class ≥ 1/(2(q+2)²)
-- statement:
--   Let $K>1$, $S\in\mathbb N$, $T\ge2K$, $\pi\in\Pi_S$, and write $q=q(S,K)$, $r=r(S,K)$. For every unit-variance Gaussian environment $\mu\in\mathbb R^K$,
--   $$\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^\pi_\mu\big(E^{(1)}_{j,k}\big)\ge\frac{K-r}{2(q+2)^2K},\qquad \frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}\mathbb P^\pi_\mu\big(E^{(2)}_{j,k}\big)\ge\frac{1}{2(q+2)^2}.$$
--
--   Under any single environment the average probability of the first class of risky events is $\widetilde\Omega((K-r)/K)$ and that of the second class is $\widetilde\Omega(1)$; applied to the reference environment $\mathbf 0$ these are the lower bounds on $\overline{q^{(1)}}$ and $\overline{q^{(2)}}$ used in (46)–(47).
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. The statement covers every $S\in\mathbb N$, including $S=0$ (where $r=-1$), which the printed proof (it uses $0\le r\le K-2$) does not treat; it holds there because Lemma 6 then gives a sum of at least $K$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, pp. 61–62, Corollary 4 (proof pp. 64–65)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Corollary 4, pp. 61–62: for every `S`-switch policy and every Gaussian environment `μ`, the
average probability of the first class of risky events is at least
`(K - r(S,K))/(2(q(S,K)+2)²K)`, and that of the second class is at least `1/(2(q(S,K)+2)²)`. -/
theorem corollary_4 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    ((K : ℝ) - (rIdx S K : ℝ)) / (2 * ((qIdx S K : ℝ) + 2) ^ 2 * K) ≤
        1 / (((qIdx S K : ℝ) + 2) * K) *
          ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
            ((banditMeasure (gaussianBandit μvec) π T) (E1 S K T j k)).toReal ∧
      1 / (2 * ((qIdx S K : ℝ) + 2) ^ 2) ≤
        1 / (((qIdx S K : ℝ) + 2) * K) *
          ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
            ((banditMeasure (gaussianBandit μvec) π T) (E2 S K T j k)).toReal := by sorry

end BwSC.LowerBound
