-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_7
-- name    : BwSC.LowerBound.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:52.747274+00:00
-- url     : https://prove2.me/theorems/726cfea4-70f8-4877-b331-279e2c047997
-- title:
--   Lemma 7, p. 61 — for every π ∈ Π_S and every environment µ: Σ_{j∈[q+2]} Σ_{k∈[K]} P^π_µ(E^(2)_{j,k}) ≥ K − 1 − ⌊S/(q(S,K)+2)⌋
-- statement:
--   Let $K>1$, $S\in\mathbb N$, $T\ge2K$, and let $\pi\in\Pi_S$. For every unit-variance Gaussian environment $\mu\in\mathbb R^K$, the second class of risky events $E^{(2)}_{j,k}$ = "action $k$ is not chosen in period $[t^{(2)}_{j-1}:t^{(2)}_j]$" satisfies
--   $$\sum_{j\in[q(S,K)+2]}\ \sum_{k\in[K]}\mathbb P^\pi_\mu\big(E^{(2)}_{j,k}\big)\ \ge\ K-1-\Big\lfloor\frac{S}{q(S,K)+2}\Big\rfloor .$$
--
--   This is the counting step for the second term of Theorem 2.
--
--   **Formalization Note** Rounds are 1-based as on the page: entry $s$ of a history $h\in(\{1,\dots,K\}\times\mathbb R)^T$ is round $s+1$, and a period $[n_1:n_2]$ is the set of rounds $t$ with $n_1\le t\le n_2$ and $1\le t\le T$.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 61, Lemma 7 (proof pp. 63–64); events App. J.1, p. 60

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 7, p. 61: for every `S`-switch policy and every Gaussian environment `μ`,
`Σ_{j ∈ [q+2]} Σ_{k ∈ [K]} P^π_μ(E^{(2)}_{j,k}) ≥ K - 1 - ⌊S/(q(S,K) + 2)⌋`. -/
theorem lemma_7 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (μvec : Fin K → ℝ) :
    (K : ℝ) - 1 - (⌊(S : ℝ) / ((qIdx S K : ℝ) + 2)⌋ : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit μvec) π T) (E2 S K T j k)).toReal := by sorry

end BwSC.LowerBound
