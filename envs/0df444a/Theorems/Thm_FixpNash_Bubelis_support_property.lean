-- Prove2me | Theorems.Thm_FixpNash_Bubelis_support_property
-- name    : FixpNash.Bubelis.support_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:37.338996+00:00
-- url     : https://prove2.me/theorems/a989ffd1-9388-4448-8d22-75a6edf0c5b9
-- title:
--   Proof of Lemma 7, p. 26 — in a Nash equilibrium each pure strategy earns at most the equilibrium payoff, with equality on the support
-- statement:
--   Let $\Gamma$ be a finite game in normal form: a finite set of players, a finite set $S_p$ of pure strategies for each player $p$, and payoff functions $u_p$ on pure profiles. Let $x = (x_p)_p$ be a mixed Nash equilibrium of $\Gamma$, write $u_p(x)$ for player $p$'s expected payoff and $u_p((p:j); x_{-p})$ for $p$'s expected payoff when $p$ switches to the pure strategy $j \in S_p$ while the others keep playing $x_{-p}$. Then for every player $p$ and every $j \in S_p$,
--   $$
--   u_p((p:j); x_{-p}) \le u_p(x), \qquad\text{and}\qquad x_p(j) > 0 \;\Longrightarrow\; u_p((p:j); x_{-p}) = u_p(x).
--   $$
--
--   In the proof of Lemma 7 this is applied to the auxiliary players 2 and 3 of the gadget $G_f$, whose equilibrium payoffs are called $v_2$ and $v_3$; it is the source of every inequality used there.
--
--   **Formalization Note** The statement is made for an arbitrary finite game rather than only for $G_f$. The Nash equilibrium is the mixed one of `agt_games` (`AGT.IsMixedNash`: no unilateral mixed deviation is profitable), and $u_p((p:j); x_{-p})$ is `DGPNash.NashMap.purePayoff`. The same fact is drafted in the companion mission on block matching pennies of this series.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

namespace FixpNash.Bubelis

/-- Support property of a mixed Nash equilibrium (proof of Lemma 7, p. 26): in a Nash
equilibrium `x` of a finite game, the expected payoff `u_p((p:j); x_{-p})` of every pure strategy
`j` of player `p` is at most `p`'s equilibrium payoff `u_p(x)`, with equality when `j` is in the
support of `x_p`. -/
theorem support_property {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedNash u x)
    (p : ι) (j : S p) :
    DGPNash.NashMap.purePayoff u x p j ≤ AGT.expectedPayoff u x p ∧
      (0 < x p j → DGPNash.NashMap.purePayoff u x p j = AGT.expectedPayoff u x p) := by sorry

end FixpNash.Bubelis
