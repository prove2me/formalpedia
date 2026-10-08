-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_solution_exists_unique
-- name    : BellmanDP.GoldMining.solution_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:13:35.892387+00:00
-- url     : https://prove2.me/theorems/8c60e44e-8d5b-4f3c-906d-b57c0d10891a
-- title:
--   Chapter II, Theorem 1 — existence and uniqueness of the solution of the gold-mining equation (5.1)
-- statement:
--   Let $p_1, p_2, r_1, r_2$ be real numbers with
--   $$|p_1| < 1,\quad |p_2| < 1,\qquad 0 \le r_1 < 1,\quad 0 \le r_2 < 1.$$
--   Then the functional equation
--   $$f(x,y) = \max\Bigl[p_1\bigl(r_1x + f((1-r_1)x,\,y)\bigr),\; p_2\bigl(r_2y + f(x,\,(1-r_2)y)\bigr)\Bigr], \qquad x, y \ge 0, \tag{5.1}$$
--   has a solution $f$ which is bounded in every rectangle $0 \le x \le \bar X$, $0 \le y \le \bar Y$; any two solutions bounded in every rectangle coincide on the quadrant $x, y \ge 0$; and this solution is continuous on the closed quadrant $x, y \ge 0$.
--
--   This is the existence and uniqueness theorem behind every later statement of the chapter: "the solution" of (5.1), in Theorems 2, 6 and 7, means this one.
--
--   **Formalization Note** Bellman allows signed $p_i$ here (his footnote 2: in the process they are nonnegative, but the proof covers the general equation), so the hypothesis is $|p_i| < 1$ as printed. "Continuous in any finite part of the region $x, y \ge 0$" is continuity of $(x,y) \mapsto f(x,y)$ on the closed quadrant, relative to the quadrant.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 6, Theorem 1, p. 64

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 1, p. 64: if `|p₁|, |p₂| < 1` and
`0 ≤ r₁, r₂ < 1`, there is a unique solution of (5.1) which is bounded in any rectangle
`0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`, and this solution is continuous on the closed quadrant `x, y ≥ 0`.
Uniqueness is equality on the quadrant, where (5.1) is posed. -/
theorem solution_exists_unique (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁ : |p₁| < 1) (hp₂ : |p₂| < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ < 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ < 1) :
    ∃ f : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ f ∧ BoundedOnRectangles f ∧
      ContinuousOn (Function.uncurry f) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∧
      ∀ g : ℝ → ℝ → ℝ, IsGoldMiningSolution p₁ p₂ r₁ r₂ g → BoundedOnRectangles g →
        ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → g x y = f x y := by sorry

end BellmanDP.GoldMining
