-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_6
-- name    : BwSC.LowerBound.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:48.500994+00:00
-- url     : https://prove2.me/theorems/875214cc-8a7b-47ce-8500-84a34a64071e
-- title:
--   Lemma 6, p. 61 — for every π ∈ Π_S and every environment µ: Σ_{j∈[q+2]} Σ_{k∈[K]} P^π_µ(E^(1)_{j,k}) ≥ K − ⌈S/(q(S,K)+1)⌉
-- statement:
--   Let $K>1$, $S\in\mathbb N$, $T\ge2K$, and let $\pi\in\Pi_S$ be an $S$-switch policy. For every unit-variance Gaussian environment $\mu\in\mathbb R^K$, the first class of risky events $E^{(1)}_{j,k}$ ($j\in[q(S,K)+2]$, $k\in[K]$) satisfies
--   $$\sum_{j\in[q(S,K)+2]}\ \sum_{k\in[K]}\mathbb P^\pi_\mu\big(E^{(1)}_{j,k}\big)\ \ge\ K-\Big\lceil\frac{S}{q(S,K)+1}\Big\rceil .$$
--
--   The right side is always at least $1$. Together with Lemma 7 it gives Corollary 4: under any single environment, risky events are not rare on average.
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$. The events are those of `BwSC.LowerBound.Proof`; the hypotheses $K>1$ and $T\ge2K$ are the standing assumptions of Theorem 2.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 61, Lemma 6 (proof pp. 62–63); events App. J.1, p. 60

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 6, p. 61: for every `S`-switch policy and every Gaussian environment `μ`,
`Σ_{j ∈ [q+2]} Σ_{k ∈ [K]} P^π_μ(E^{(1)}_{j,k}) ≥ K - ⌈S/(q(S,K) + 1)⌉`. -/
theorem lemma_6 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    (K : ℝ) - (⌈(S : ℝ) / ((qIdx S K : ℝ) + 1)⌉ : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E1 S K T j k)).toReal := by sorry

end BwSC.LowerBound
