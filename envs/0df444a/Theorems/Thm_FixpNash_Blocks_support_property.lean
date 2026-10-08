-- Prove2me | Theorems.Thm_FixpNash_Blocks_support_property
-- name    : FixpNash.Blocks.support_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:36.192378+00:00
-- url     : https://prove2.me/theorems/500f72c1-64a9-403f-a777-3e6e8a6d07f3
-- title:
--   p. 26 — in a Nash equilibrium every pure strategy earns at most the equilibrium payoff, with equality on the support
-- statement:
--   Let $u$ be a finite game in normal form and let $x$ be a mixed Nash equilibrium of $u$: each $x_p$ is a probability distribution on $S_p$, and no player can increase their expected payoff by unilaterally switching to another mixed strategy. Write $u_p(x)$ for the expected payoff of player $p$ under $x$ and $u_p((p{:}j);x_{-p})$ for the expected payoff of player $p$ when they play the pure strategy $j$ and the other players play according to $x$. Then for every player $p$ and every $j\in S_p$,
--   $$
--   u_p((p{:}j);x_{-p})\le u_p(x),\qquad\text{with equality if } x_p(j)>0 .
--   $$
--
--   This is the elementary support characterization of Nash equilibria. Etessami and Yannakakis state it on p. 26 (proof of Lemma 7) for the two players of Bubelis's gadget, and use it twice in the proof of Lemma 6 (p. 24): to show that the matching player $i'$ avoids the most probable blocks, and that player $i$ puts no probability on strategies with a low payoff.
--
--   **Formalization Note.** The paper's sentence speaks of players 2 and 3 of a specific game; the statement here is the same fact for every player of every finite game, which is the form in which the proof of Lemma 6 uses it. "In the support of $x$" is read as $x_p(j)>0$. The quantity $u_p((p{:}j);x_{-p})$ is `DGPNash.NashMap.purePayoff`.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26 (used in the proof of Lemma 6, p. 24)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

namespace FixpNash.Blocks

/-- Support property of a mixed Nash equilibrium (Etessami–Yannakakis, p. 26, proof of
Lemma 7; used twice in the proof of Lemma 6, p. 24): in a Nash equilibrium `x` of a finite
game, the expected payoff `u_p((p:j); x_{-p})` of every pure strategy `j` of every player
`p` is at most `p`'s equilibrium payoff, with equality if `j` is in the support of `x`. -/
theorem support_property {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedNash u x)
    (p : ι) (j : S p) :
    DGPNash.NashMap.purePayoff u x p j ≤ AGT.expectedPayoff u x p ∧
      (0 < x p j → DGPNash.NashMap.purePayoff u x p j = AGT.expectedPayoff u x p) := by sorry

end FixpNash.Blocks
