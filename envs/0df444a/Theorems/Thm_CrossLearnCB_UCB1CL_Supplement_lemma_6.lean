-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_lemma_6
-- name    : CrossLearnCB.UCB1CL.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:55:56.536274+00:00
-- url     : https://prove2.me/theorems/63c22ed1-5857-4fba-a72d-213d9915d47e
-- title:
--   Lemma 6, p. 51 — a hard distribution forces Ω(√(K/T)) expected pseudo-regret in every round
-- statement:
--   There is an absolute $a>0$ such that for every $K\ge2$ and all sufficiently large $T$, a uniform finite distribution over stochastic $K$-arm, single-context instances with independent reward coordinates has the following property: every randomized measurable policy and every round $t<T$ satisfy
--   $$\mathbb E[\mu^*-\mu_{I_t}]\ge a\sqrt{K/T}.$$
--   The expectation includes the instance draw, reward draws and the algorithm's randomness. The distribution is chosen before the policy and works simultaneously for all rounds. This is the support lemma in the proof of Theorem 5.
--
--   **Formalization Note** The horizon threshold depends on $K$. One context represents the non-contextual problem, and the complete one-context graph reveals exactly the played arm reward. The instance family is averaged explicitly, with normalization $1/m$.
--
--   Differences from the source:
--   - encoding: an Ω lower bound → one absolute positive real constant, then every fixed dimension/graph has a positive horizon threshold, and every larger horizon satisfies the bound; reason: the meaning of the asymptotic rate; constants never depend on the horizon, instance, dimensions or policy
--   - reading: multi-armed bandits with a nonzero asymptotic lower bound → K ≥ 2, C > 0 and a positive horizon threshold; reason: one arm has identically zero regret and no positive context law exists on an empty set; thresholds exclude only the small-horizon regime, where an uncapped square-root lower bound can exceed T
--   - encoding: any randomized algorithm and its expected regret → valid measurable behavioural policies with the masked feedback record, finite arm/context sums, and integrals over bounded reward tables; reason: the protocol has perfect recall; behavioural policies describe the same observable strategies and measurability makes the source expectations defined
--   - encoding: there exists a distribution over hard instances → a uniform finite family S indexed by Fin m, m > 0; reason: Appendix C.7 selects the best arm uniformly from K independent Bernoulli instances; this is a witness of the source existential, rather than a restriction on algorithms
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 51, Lemma 6

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_RoundRegret

namespace CrossLearnCB.UCB1CL.Supplement

/-- Lemma 6, p. 51. A finite uniform distribution over stochastic one-context instances
forces Ω(√(K/T)) expected pseudo-regret in every round, for every algorithm. -/
theorem lemma_6 : ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) [NeZero K], 2 ≤ K →
    ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
    ∃ m : ℕ, 0 < m ∧ ∃ S : Fin m → StochInstance K 1,
      (∀ j, (S j).IsCoordinateIndependent) ∧ ∀ A : Policy K 1, A.IsValid → A.IsMeasurable → ∀ t : Fin T,
        c * Real.sqrt ((K : ℝ) / T) ≤
          (1 / (m : ℝ)) * ∑ j : Fin m, roundStochRegret t (fun _ _ _ => True) (S j) A := by sorry

end CrossLearnCB.UCB1CL.Supplement
