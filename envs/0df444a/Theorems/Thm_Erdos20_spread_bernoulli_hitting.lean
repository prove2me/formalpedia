-- Prove2me | Theorems.Thm_Erdos20_spread_bernoulli_hitting
-- name    : Erdos20.spread_bernoulli_hitting
-- status  : Proved
-- author  : @lunjia
-- created : 2026-09-26T16:17:22.765454+00:00
-- url     : https://prove2.me/theorems/1d8c57c6-69da-4fb8-b957-6896f1669cc3
-- title:
--   A Bernoulli sample hits a logarithmically spread family
-- statement:
--   There is an absolute constant $C\ge4$ such that the following holds for all integers $n,k\ge2$. Let $X$ be a finite ground set and let $\mathcal F$ be a nonempty finite family of subsets of $X$, each of cardinality at most $n$. Suppose $\mathcal F$ is normalized $R$-spread for $R=Ck\log n$:
--
--   $$R^{|T|}\,|\{A\in\mathcal F:T\subseteq A\}|\le|\mathcal F|\quad\text{for every }T\subseteq X.$$
--
--   If $W\subseteq X$ includes each element independently with probability $1/(2k)$, then
--
--   $$\Pr(\exists A\in\mathcal F:\ A\subseteq W)\ge\tfrac12.$$
--
--   Empty members are allowed; if the family contains the empty set, the event has probability one. The constant is independent of the ground set, the family, the rank bound, and the desired number of petals. Logarithms are natural.
--
--   **Source formulation.** This is the bounded-rank, normalized-spread adaptation of the random-set hitting estimate underlying the BCW coloring argument, using Hu/Tao refinement and iteration. It is not a verbatim statement of BCW's absolute-spread uniform-family lemma, nor of Hu's fixed-cardinality sampling lemma. The local self-contained two-chain derivation uses Bernoulli sampling throughout and supports $C=256$.
-- source:
--   L. Hu, Entropy Estimation via Two Chains (19 May 2021), Definition 1 and Lemma 2, https://theorydish.blog/2021/05/19/entropy-estimation-via-two-chains-streamlining-the-proof-of-the-sunflower-lemma/ ; T. Tao, The sunflower lemma via Shannon entropy (2020), refinement and iteration, https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ ; Bell, Chueluecha, Warnke, Note on Sunflowers, arXiv:2009.09327v2, Theorem 3 and proof of Lemma 2, https://arxiv.org/html/2009.09327v2 . Normalized bounded-rank Bernoulli adaptation as explicitly described.

import Definitions.Def_SunflowerSpread
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace Erdos20

/-- The one-petal probabilistic estimate. Empty family members are permitted,
since in that case the hitting event is certain. -/
theorem spread_bernoulli_hitting :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      ∀ {α : Type} [Fintype α] [DecidableEq α] (F : Finset (Finset α)),
        F.Nonempty → (∀ A ∈ F, A.card ≤ n) →
        IsSpread (C * k * Real.log n) F →
        ∀ p : unitInterval, (p : ℝ) = (2 * (k : ℝ))⁻¹ →
          (1 / 2 : ℝ) ≤ (ProbabilityTheory.setBernoulli (Set.univ : Set α) p).real
            {W | ∃ A ∈ F, (A : Set α) ⊆ W} := by
  sorry

end Erdos20
