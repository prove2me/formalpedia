-- Prove2me | Theorems.Thm_FixpNash_DivFree_threshold_eq_expectedPayoff
-- name    : FixpNash.DivFree.threshold_eq_expectedPayoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:35.027837+00:00
-- url     : https://prove2.me/theorems/92b9bdbe-d15e-48c5-b0b8-8463dce68ff2
-- title:
--   Proof of Lemma 20, p. 47 — at a Nash equilibrium, t_i = r_i = u_i(x)
-- statement:
--   Consider a finite game in which every player has a nonempty set of pure strategies, and let $x$ be a Nash equilibrium. Write $r_i=u_i(x)$ for the expected payoff of player $i$ in $x$. Then for every player $i$ the threshold $t_i$ of the map $G_I$ at $x$ equals $r_i$:
--   $$t_i=r_i=u_i(x).$$
--
--   This is the key step of the second half of the proof of Lemma 20: at an equilibrium $x_{ij}=\max(x_{ij}+v(x)_{ij}-r_i,0)$ for all $i,j$, hence $f_{i,x}(r_i)=1$, so $r_i$ is the threshold, and $G_I(x)=x$ follows.
--
--   **Formalization Note.** $t_i$ is the threshold of the definition file, the unique root of $f_{i,x}(t)=1$. Every strategy set is assumed nonempty, the paper's tacit assumption.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, proof of Lemma 20, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- Proof of Lemma 20, p. 47: at a Nash equilibrium `x`, the threshold `tᵢ` equals
player `i`'s expected payoff `rᵢ = uᵢ(x)`. -/
theorem threshold_eq_expectedPayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (hS : ∀ i, Nonempty (S i)) (x : ∀ i, S i → ℝ)
    (hNE : AGT.IsMixedNash u x) :
    ∀ i : ι, threshold u x i = AGT.expectedPayoff u x i := by sorry

end FixpNash.DivFree
