-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_proj_properties
-- name    : CalamaiMore.Convergence.proj_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:29:56.35565+00:00
-- url     : https://prove2.me/theorems/d20c7ea3-d615-406c-a0dd-32abd654f752
-- title:
--   Lemma 2.1 — variational inequality, monotonicity and nonexpansiveness of the projection
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, and let $P$ be the projection into $\Omega$.
--
--   1. If $z \in \Omega$, then $\langle P(x) - x, z - P(x) \rangle \ge 0$ for all $x \in E$.
--   2. $P$ is monotone: $\langle P(y) - P(x), y - x \rangle \ge 0$ for all $x, y \in E$, and the inequality is strict whenever $P(y) \ne P(x)$.
--   3. $P$ is nonexpansive:
--   $$
--   \|P(y) - P(x)\| \le \|y - x\| \quad \text{for all } x, y \in E.
--   $$
--
--   These three properties of the projection underlie every estimate in the convergence analysis of the gradient projection method.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Lemma 2.1

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Lemma 2.1 (p. 98): (a) the variational inequality of the projection,
(b) monotonicity (strict when the projections differ), (c) nonexpansiveness. -/
theorem proj_properties {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω) :
    (∀ x : E, ∀ z ∈ Ω, 0 ≤ inner ℝ (proj Ω x - x) (z - proj Ω x)) ∧
    (∀ x y : E, 0 ≤ inner ℝ (proj Ω y - proj Ω x) (y - x) ∧
      (proj Ω y ≠ proj Ω x → 0 < inner ℝ (proj Ω y - proj Ω x) (y - x))) ∧
    (∀ x y : E, ‖proj Ω y - proj Ω x‖ ≤ ‖y - x‖) := by sorry

end CalamaiMore.Convergence
