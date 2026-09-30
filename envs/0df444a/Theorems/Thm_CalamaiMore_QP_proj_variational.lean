-- Prove2me | Theorems.Thm_CalamaiMore_QP_proj_variational
-- name    : CalamaiMore.QP.proj_variational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:59:29.557986+00:00
-- url     : https://prove2.me/theorems/216aa880-23c8-4302-b996-2ca81092783a
-- title:
--   Lemma 2.1(a) — variational inequality of the projection
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$ and let $P$ be the projection into $\Omega$. If $z \in \Omega$, then
--
--   $$
--   \langle P(x) - x,\ z - P(x) \rangle \ge 0 \qquad \text{for all } x \in E.
--   $$
--
--   Geometrically, the vector from $x$ to its projection makes a non-obtuse angle with every direction from $P(x)$ into $\Omega$. This inequality is the source of the descent estimates (2.4)–(2.5) of the gradient projection method, and it characterises the fixed points of $x \mapsto P(x - \alpha\nabla f(x))$ as the stationary points.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Lemma 2.1(a)

import Mathlib
import Definitions.Def_CalamaiMore_QP_proj

namespace CalamaiMore.QP

/-- Calamai–Moré, Lemma 2.1(a) (p. 98): for a nonempty closed convex `Ω`, if `z ∈ Ω` then
`⟨P(x) - x, z - P(x)⟩ ≥ 0` for all `x`. -/
theorem proj_variational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (z : E) (hz : z ∈ Ω) (x : E) :
    0 ≤ inner ℝ (proj Ω x - x) (z - proj Ω x) := by sorry

end CalamaiMore.QP
