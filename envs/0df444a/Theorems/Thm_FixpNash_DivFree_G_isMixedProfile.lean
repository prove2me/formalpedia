-- Prove2me | Theorems.Thm_FixpNash_DivFree_G_isMixedProfile
-- name    : FixpNash.DivFree.G_isMixedProfile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:57.984211+00:00
-- url     : https://prove2.me/theorems/0bb4369b-63c9-4316-99a6-202693e1b9dc
-- title:
--   p. 47 — Σ_j G_I(x)_ij = 1, so G_I(x) lies in Δ
-- statement:
--   Consider a finite game in which every player has a nonempty set of pure strategies, and let $x$ be any real vector indexed by player–strategy pairs. Then $G_I(x)$, defined by $G_I(x)_{ij}=\max(h_{ij}(x)-t_i,0)$, is a mixed strategy profile: for every player $i$,
--   $$G_I(x)_{ij}\ge 0\ \ (j\in S_i)\qquad\text{and}\qquad \sum_{j\in S_i}G_I(x)_{ij}=1 .$$
--
--   In the paper this is the remark that, by the choice of $t_i$, the map $G_I$ sends its domain $\Delta$ into itself, so that $G_I$ is a self-map of a compact convex set and its fixed points are meaningful.
--
--   **Formalization Note.** The paper states the sum identity and concludes $G_I(x)\in\Delta$; the Lean conclusion is the membership $G_I(x)\in\Delta$ (`AGT.IsMixedProfile`), which contains the sum identity and the nonnegativity that is immediate from the $\max$. It is stated for every real $x$, a slight generalization of $x\in\Delta$. Every strategy set is assumed nonempty, the paper's tacit assumption.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, definition of G_I, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- p. 47: `∑_{j ∈ Sᵢ} G_I(x)ᵢⱼ = 1` for every player `i`, so `G_I(x)` lies in `Δ`
(its entries are nonnegative by construction). Holds for every real vector `x`. -/
theorem G_isMixedProfile {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (hS : ∀ i, Nonempty (S i)) (x : ∀ i, S i → ℝ) :
    AGT.IsMixedProfile (G u x) := by sorry

end FixpNash.DivFree
