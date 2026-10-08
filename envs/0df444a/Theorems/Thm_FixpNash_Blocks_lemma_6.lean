-- Prove2me | Theorems.Thm_FixpNash_Blocks_lemma_6
-- name    : FixpNash.Blocks.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:16.173541+00:00
-- url     : https://prove2.me/theorems/ed70586f-ed83-46e0-8f31-e27812e7cac3
-- title:
--   Lemma 6 (p. 24) — block matching pennies: equal block probabilities and full support for i′ in every Nash equilibrium
-- statement:
--   Let $G$ be a finite game with a pair of players $i\neq i'$ such that the pure strategies of $i$ are partitioned into blocks, the blocks are in one-to-one correspondence with the pure strategies of $i'$ (via a surjective map $\beta:S_i\to S_{i'}$ sending a strategy to the strategy of $i'$ that its block corresponds to), and the payoffs of $i,i'$ have the form
--   $$
--   u_i(s)=\mu(s)+M\cdot[\beta(s_i)=s_{i'}],\qquad u_{i'}(s)=-M\cdot[s_{i'}=\beta(s_i)],
--   $$
--   where $\mu$ does not depend on $s_{i'}$, $M>6n\max_s|\mu(s)|$, and $i'$ has at most $3n$ strategies. Then every mixed Nash equilibrium $x$ of $G$ has the following properties.
--   1. The total probability allocated to the strategies in each block of player $i$ is the same for all the blocks: $\sum_{j:\beta(j)=k}x_i(j)=\sum_{j:\beta(j)=k'}x_i(j)$ for all $k,k'\in S_{i'}$.
--   2. All strategies of player $i'$ have nonzero probability: $x_{i'}(k)\neq 0$ for all $k\in S_{i'}$.
--
--   In the reduction of Section 3 of Etessami and Yannakakis (Step 2 of the proof of Theorem 4), which encodes the gates of an arithmetic circuit into a game, this lemma is what forces every unprimed player to divide its probability evenly among its blocks, so that the probabilities inside a block can encode the value of a circuit gate.
--
--   **Formalization Note.** The game is the `agt_games` vocabulary (finite players and strategy types, real payoffs, `AGT.IsMixedNash` with deviations to arbitrary mixed strategies). The hypothesis "the payoffs of $i,i'$ are of the form given above" is the predicate `FixpNash.Blocks.IsBlockPair`; it includes the bound "$i'$ has at most $3n$ strategies", which the paper's proof uses ("since $i'$ has at most $3n$ strategies", p. 24), and the condition that $\mu$ does not depend on $s_{i'}$, which the proof does not use. "Nonzero probability" is stated as $x_{i'}(k)\neq 0$, equivalent to $x_{i'}(k)>0$ for a probability vector.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Lemma 6, p. 24 (payoff form pp. 23–24)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Blocks_Form

namespace FixpNash.Blocks

/-- Lemma 6 (Etessami–Yannakakis, p. 24): if the players `i, i'` of a finite game form a
block matching-pennies pair of the form given on pp. 23–24, then every Nash equilibrium
`x` satisfies
1. the total probability allocated to the strategies in each block of player `i` is the
   same for all the blocks;
2. all strategies of player `i'` have nonzero probability. -/
theorem lemma_6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedNash u x) :
    (∀ k k' : S i', blockProb β x k = blockProb β x k') ∧ (∀ k : S i', x i' k ≠ 0) := by sorry

end FixpNash.Blocks
