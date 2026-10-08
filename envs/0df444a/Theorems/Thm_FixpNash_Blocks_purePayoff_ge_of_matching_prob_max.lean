-- Prove2me | Theorems.Thm_FixpNash_Blocks_purePayoff_ge_of_matching_prob_max
-- name    : FixpNash.Blocks.purePayoff_ge_of_matching_prob_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:00.72056+00:00
-- url     : https://prove2.me/theorems/3498e101-bfcb-4869-8dbf-032142ff8ec2
-- title:
--   p. 24, proof of Lemma 6 — a strategy whose block matches a most probable strategy of i′ earns at least M/3n − maxₛ|μ(s)|
-- statement:
--   Let players $i,i'$ of a finite game form a block matching-pennies pair (block map $\beta$, first term $\mu$, constant $M$, parameter $n$, so in particular $i'$ has at most $3n$ strategies), and let $x$ be any mixed profile. Let $j'\in S_i$ be a strategy of $i$ whose block corresponds to a maximum-probability strategy of $i'$: $x_{i'}(k)\le x_{i'}(\beta(j'))$ for every $k\in S_{i'}$. Then
--   $$
--   u_i((i{:}j');x_{-i})\ \ge\ \frac{M}{3n}-\max_s|\mu(s)| .
--   $$
--
--   Together with the companion upper bound $\max_s|\mu(s)|$ for strategies whose matching strategy has probability $0$, and the choice $M>6n\max_s|\mu(s)|$, this shows that such strategies are strictly worse than $j'$ for player $i$.
--
--   **Formalization Note.** The paper writes $M/3n$, meaning $M/(3n)$. $\max_s|\mu(s)|$ is the supremum of $|\mu(s)|$ over the finite set of pure profiles.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 6, part 1, p. 24

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_Blocks_Form

namespace FixpNash.Blocks

/-- Proof of Lemma 6, p. 24, second payoff bound: for any mixed profile `x`, if the block
of the strategy `j'` of `i` corresponds to a maximum-probability strategy `β j'` of `i'`,
then the expected payoff of `j'` for player `i` against the rest of `x` is at least
`M/(3n) - max_s |μ(s)|`. -/
theorem purePayoff_ge_of_matching_prob_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (i i' : ι) (β : S i → S i')
    (μ : (∀ k, S k) → ℝ) (M : ℝ) (n : ℕ) (hG : IsBlockPair u i i' β μ M n)
    (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedProfile x)
    (j' : S i) (hj' : ∀ k : S i', x i' k ≤ x i' (β j')) :
    M / (3 * (n : ℝ)) - (⨆ s : (∀ k, S k), |μ s|) ≤ DGPNash.NashMap.purePayoff u x i j' := by sorry

end FixpNash.Blocks
