-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_tangentCone_polyhedron
-- name    : CalamaiMore.ActiveSet.tangentCone_polyhedron
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:54:44.082742+00:00
-- url     : https://prove2.me/theorems/582f3642-d85c-4065-ad65-cd689a5b58f4
-- title:
--   The tangent cone of a polyhedral set, §4 p. 105
-- statement:
--   Let $\Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be a polyhedral set in a finite-dimensional real inner product space $E$, with active sets $A(x) = \{j : \langle c_j, x \rangle = \delta_j\}$. For every $x \in \Omega$ the tangent cone of $\Omega$ at $x$ (the closure of the cone of feasible directions) is
--
--   $$
--   T(x) = \{v \in E : \langle c_j, v \rangle \ge 0,\ j \in A(x)\}.
--   $$
--
--   Only the active constraints restrict the directions in which one can move from $x$; this formula is what connects the projected gradient to the active set.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 105, §4, display after Eq. (4.2)

import Mathlib
import Definitions.Def_CalamaiMore_Shared_tangentCone
import Definitions.Def_CalamaiMore_ActiveSet_polyhedron

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, §4, p. 105 (display after (4.2)): for the polyhedral set
`Ω = {x : ⟨c_j, x⟩ ≥ δ_j}` and `x ∈ Ω`, the tangent cone is
`T(x) = {v : ⟨c_j, v⟩ ≥ 0, j ∈ A(x)}`. -/
theorem tangentCone_polyhedron {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (x : E) (hx : x ∈ polyhedron c δ) :
    CalamaiMore.Shared.tangentCone (polyhedron c δ) x =
      {v | ∀ j ∈ activeSet c δ x, 0 ≤ inner ℝ (c j) v} := by sorry

end CalamaiMore.ActiveSet
