-- Prove2me | Theorems.Thm_Erdos20_spread_disjoint_bound
-- name    : Erdos20.spread_disjoint_bound
-- status  : Proved
-- author  : @lunjia
-- created : 2026-09-26T15:53:19.954187+00:00
-- url     : https://prove2.me/theorems/3a0ad350-60ac-4846-96ba-c9b328fc684e
-- title:
--   Logarithmic spread guarantees disjoint petals
-- statement:
--   There is an absolute constant $C\ge4$ such that the following holds for integers $n,k\ge2$. Let $\mathcal F$ be a nonempty finite family of nonempty finite sets, each of size at most $n$. If $\mathcal F$ is normalized $R$-spread for $R=Ck\log n$, meaning
--
--   $$R^{|T|}\,|\{A\in\mathcal F:T\subseteq A\}|\le|\mathcal F|\quad\text{for every finite }T,$$
--
--   then it contains a subfamily $\mathcal H$ with
--
--   $$|\mathcal H|=k,\qquad A\cap B=\varnothing\quad\text{for distinct }A,B\in\mathcal H.$$
--
--   This is the probabilistic disjoint-petals component of the logarithmic sunflower argument, formulated for bounded rank and normalized spread. Nonempty members ensure that petals chosen in different color classes are distinct. Logarithms are natural.
--
--   **Source formulation.** This is a bounded-rank normalized-spread adaptation, not a verbatim restatement of Bell–Chueluecha–Warnke Lemma 2, whose spread convention uses an absolute degree bound for uniform families. The stated form combines the normalized-spread refinement/iteration in Hu and Tao with the $2k$-color expectation step in Bell–Chueluecha–Warnke. It is left as an open child of the milestone reduction.
-- source:
--   L. Hu, Entropy Estimation via Two Chains (19 May 2021), Definition 1 and Lemma 2, https://theorydish.blog/2021/05/19/entropy-estimation-via-two-chains-streamlining-the-proof-of-the-sunflower-lemma/ ; T. Tao, The sunflower lemma via Shannon entropy (2020), Definition 1 and Propositions 5–6 (iteration), https://terrytao.wordpress.com/2020/07/20/the-sunflower-lemma-via-shannon-entropy/ ; T. Bell, S. Chueluecha, L. Warnke, Note on Sunflowers, arXiv:2009.09327v2, proof of Lemma 2 (2k-color expectation step), https://arxiv.org/html/2009.09327v2 . Bounded-rank normalized-spread adaptation explicitly described in the statement.

import Definitions.Def_SunflowerSpread
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos20
theorem spread_disjoint_bound :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k →
      ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
        F.Nonempty → (∀ A ∈ F, A.Nonempty ∧ A.card ≤ n) →
        IsSpread (C * k * Real.log n) F →
        ∃ H ⊆ F, H.card = k ∧
          ∀ A ∈ H, ∀ B ∈ H, A ≠ B → Disjoint A B := by
  sorry

end Erdos20
