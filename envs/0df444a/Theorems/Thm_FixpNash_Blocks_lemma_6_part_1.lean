-- Prove2me | Theorems.Thm_FixpNash_Blocks_lemma_6_part_1
-- name    : FixpNash.Blocks.lemma_6_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:04.322547+00:00
-- url     : https://prove2.me/theorems/1dfeec37-3661-4db4-9fb0-308a0283740c
-- title:
--   Lemma 6, part 1 (p. 24) — in every Nash equilibrium all blocks of player i have the same total probability
-- statement:
--   Let players $i,i'$ of a finite game form a block matching-pennies pair (block map $\beta:S_i\to S_{i'}$, first term $\mu$, constant $M$, parameter $n$), and let $x$ be a mixed Nash equilibrium. Then all blocks of player $i$ have the same total probability:
--   $$
--   \sum_{j:\beta(j)=k}x_i(j)=\sum_{j:\beta(j)=k'}x_i(j)\qquad\text{for all }k,k'\in S_{i'} .
--   $$
--   Since the blocks partition $S_i$ and there are $|S_{i'}|$ of them, each block then has probability $1/|S_{i'}|$. Part 2 of Lemma 6 is derived from this statement.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Lemma 6, part 1, and the end of its proof, p. 24

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Blocks_Form

namespace FixpNash.Blocks

/-- Lemma 6, part 1 (p. 24): in every Nash equilibrium `x`, all blocks of player `i` have
the same total probability. -/
theorem lemma_6_part_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedNash u x) :
    ∀ k k' : S i', blockProb β x k = blockProb β x k' := by sorry

end FixpNash.Blocks
