-- Prove2me | Theorems.Thm_FixpNash_Blocks_matching_prob_zero_of_max_block
-- name    : FixpNash.Blocks.matching_prob_zero_of_max_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:43.175494+00:00
-- url     : https://prove2.me/theorems/e165ca30-e346-4630-98ef-5dd14d8e7832
-- title:
--   p. 24, proof of Lemma 6 — if the blocks are unequal, i′ puts probability 0 on the strategies matching maximum-probability blocks
-- statement:
--   Let players $i,i'$ of a finite game form a block matching-pennies pair (block map $\beta:S_i\to S_{i'}$, first term $\mu$, constant $M$, parameter $n$; see the definition item), and let $x$ be a mixed Nash equilibrium. Write $b_k(x)=\sum_{j:\beta(j)=k}x_i(j)$ for the total probability of block $k$. Suppose that the block probabilities are not all equal, and let $k\in S_{i'}$ be a strategy of $i'$ whose block has maximum total probability:
--   $$
--   \exists\,k_1,k_2:\ b_{k_1}(x)\ne b_{k_2}(x),\qquad b_{k'}(x)\le b_k(x)\ \text{ for all }k' .
--   $$
--   Then
--   $$
--   x_{i'}(k)=0 .
--   $$
--
--   In the paper's words: if $R$ is the set of blocks of maximum probability, the strategies of $i'$ corresponding to blocks in $R$ have probability $0$, because otherwise $i'$ could improve its expected payoff. This is the first step of the proof of Lemma 6, part 1.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 6, part 1, p. 24

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Blocks_Form

namespace FixpNash.Blocks

/-- Proof of Lemma 6, p. 24: if a Nash equilibrium `x` gives unequal total probability to
some blocks of player `i`, then every strategy `k` of `i'` whose block has maximum total
probability gets probability `0` in `x`. -/
theorem matching_prob_zero_of_max_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedNash u x)
    (hunequal : ∃ k₁ k₂ : S i', blockProb β x k₁ ≠ blockProb β x k₂)
    (k : S i') (hk : ∀ k' : S i', blockProb β x k' ≤ blockProb β x k) :
    x i' k = 0 := by sorry

end FixpNash.Blocks
