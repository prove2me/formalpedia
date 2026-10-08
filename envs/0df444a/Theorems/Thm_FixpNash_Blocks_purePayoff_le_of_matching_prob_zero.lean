-- Prove2me | Theorems.Thm_FixpNash_Blocks_purePayoff_le_of_matching_prob_zero
-- name    : FixpNash.Blocks.purePayoff_le_of_matching_prob_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:03.169427+00:00
-- url     : https://prove2.me/theorems/bddcaef3-dc1c-4f0c-a385-f75748682714
-- title:
--   p. 24, proof of Lemma 6 — a strategy whose block's matching strategy has probability 0 earns at most maxₛ|μ(s)|
-- statement:
--   Let players $i,i'$ of a finite game form a block matching-pennies pair (block map $\beta$, first term $\mu$, constant $M$, parameter $n$), and let $x$ be any mixed profile (not necessarily an equilibrium). Let $j\in S_i$ be a strategy of $i$ whose block corresponds to a strategy of $i'$ that has probability $0$ in $x$, i.e. $x_{i'}(\beta(j))=0$. Then the expected payoff of $j$ for player $i$ against the rest of the profile satisfies
--   $$
--   u_i((i{:}j);x_{-i})\le \max_s|\mu(s)| .
--   $$
--
--   In the proof of Lemma 6 this is applied to strategies in a block of maximum probability, whose matching strategies of $i'$ have probability $0$ by the preceding step; the statement here isolates the only property of such blocks that the bound uses.
--
--   **Formalization Note.** $\max_s|\mu(s)|$ is the supremum of $|\mu(s)|$ over the finite set of pure profiles. The paper's sentence speaks of "any strategy in a block in $R$"; the hypothesis $x_{i'}(\beta(j))=0$ is the general form of it.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 6, part 1, p. 24

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_Blocks_Form

namespace FixpNash.Blocks

/-- Proof of Lemma 6, p. 24, first payoff bound: for any mixed profile `x`, if the
strategy `β j` of `i'` corresponding to the block of the strategy `j` of `i` has
probability `0`, then the expected payoff of `j` for player `i` against the rest of `x`
is at most `max_s |μ(s)|`. -/
theorem purePayoff_le_of_matching_prob_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedProfile x)
    (j : S i) (hj : x i' (β j) = 0) :
    DGPNash.NashMap.purePayoff u x i j ≤ ⨆ s : (∀ k, S k), |μ s| := by sorry

end FixpNash.Blocks
