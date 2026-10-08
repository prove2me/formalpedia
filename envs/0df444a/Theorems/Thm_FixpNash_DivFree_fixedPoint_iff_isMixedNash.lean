-- Prove2me | Theorems.Thm_FixpNash_DivFree_fixedPoint_iff_isMixedNash
-- name    : FixpNash.DivFree.fixedPoint_iff_isMixedNash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:39.373019+00:00
-- url     : https://prove2.me/theorems/5f4b683c-307b-403d-be8c-ed8ae474e118
-- title:
--   Lemma 20 — the fixed points of G_I are precisely the Nash equilibria
-- statement:
--   Let $I$ be a finite game in which every player has a nonempty set of pure strategies, let $\Delta$ be the set of mixed strategy profiles, and let $G_I$ be the map $G_I(x)_{ij}=\max\bigl(x_{ij}+u_i((i{:}j);x_{-i})-t_i,\,0\bigr)$, where $t_i$ is the unique real number with $\sum_{j\in S_i}\max\bigl(x_{ij}+u_i((i{:}j);x_{-i})-t_i,0\bigr)=1$. For every $x\in\Delta$,
--   $$G_I(x)=x\iff x\text{ is a Nash equilibrium of }I .$$
--   That is, the fixed points of $G_I$ are precisely the Nash equilibria of the game.
--
--   Since $G_I$ is a continuous self-map of the compact convex set $\Delta$, the lemma gives an elementary proof of Nash's theorem through Brouwer's fixed point theorem, and, because $G_I$ needs no division, it shows that the class FIXP is unchanged when division is removed from the circuits (Theorem 22).
--
--   **Formalization Note.** A "fixed point of $G_I$" is a point of its domain $\Delta$ with $G_I(x)=x$, hence the hypothesis $x\in\Delta$. Nash equilibrium is the published `AGT.IsMixedNash` (deviations to arbitrary mixed strategies). Every strategy set is assumed nonempty, the paper's tacit assumption (otherwise $\Delta$ is empty and $t_i$ does not exist). Payoffs are real, a generalization of the paper's rational payoffs.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, Lemma 20, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- Lemma 20, p. 47: the fixed points of `G_I` in its domain `Δ` are precisely the
Nash equilibria of the game. -/
theorem fixedPoint_iff_isMixedNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (hS : ∀ i, Nonempty (S i)) (x : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) :
    G u x = x ↔ AGT.IsMixedNash u x := by sorry

end FixpNash.DivFree
