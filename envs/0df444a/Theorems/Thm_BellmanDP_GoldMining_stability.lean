-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_stability
-- name    : BellmanDP.GoldMining.stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:14:37.604986+00:00
-- url     : https://prove2.me/theorems/82fbd9e3-2a99-4619-a8a9-b4acc3a43125
-- title:
--   Chapter II, Theorem 7 — stability: $|f-g|\le \max_R|h|/q$ with $q=\min(1-p_1,1-p_2)$
-- statement:
--   Let $0 \le p_1, p_2 < 1$ and $0 \le r_1, r_2 \le 1$. Let $f$ be the solution of (5.1), and let $g$ be the solution of the perturbed equation
--   $$g(x,y) = \max\Bigl[A: p_1\bigl(r_1x + g((1-r_1)x,y)\bigr),\; B: p_2\bigl(r_2y + g(x,(1-r_2)y)\bigr)\Bigr] + h(x,y), \qquad x, y \ge 0,$$
--   where $h$ is bounded in every rectangle, both solutions being taken in the class of functions bounded in every rectangle. Then in any rectangle $R: 0 \le x \le \bar X,\ 0 \le y \le \bar Y$,
--   $$|f(x,y) - g(x,y)| \le \frac{\max_R |h(x,y)|}{q}, \qquad q = \min\bigl(1-p_1,\,1-p_2\bigr).$$
--
--   The solution therefore depends continuously on a perturbation of the equation, uniformly on rectangles.
--
--   **Formalization Note** The book places no condition on $h$; the hypothesis that $h$ is bounded in every rectangle is added because it is what makes the perturbed equation have a solution in the class (the book's footnote 7: "the solution" is the unique solution in the appropriate function class). $\max_R|h|$ is written through an arbitrary bound $M$ of $|h|$ on $R$, which is equivalent and avoids taking a supremum. The parameter ranges are those of § 8 and Theorem 2.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 14, Theorem 7, p. 76

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 7, p. 76: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1`, let `f` be the solution of (5.1) and `g` the solution of the perturbed
equation (2), both in the class of functions bounded in every rectangle, with `h` bounded in every
rectangle (the hypothesis under which (2) has a solution in that class). Then in any rectangle
`R: 0 ≤ x ≤ X̄, 0 ≤ y ≤ Ȳ`, `|f(x, y) − g(x, y)| ≤ Max_R |h(x, y)| / q` with
`q = Min((1 − p₁), (1 − p₂))`; the maximum of `|h|` over `R` is written as an arbitrary bound `M`
of `|h|` on `R`. -/
theorem stability (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (h : ℝ → ℝ → ℝ) (hh : BoundedOnRectangles h)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (g : ℝ → ℝ → ℝ) (hg : IsPerturbedSolution p₁ p₂ r₁ r₂ h g) (hgb : BoundedOnRectangles g)
    (X Y M : ℝ) (hM : ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y → |h x y| ≤ M) :
    ∀ x y : ℝ, 0 ≤ x → x ≤ X → 0 ≤ y → y ≤ Y →
      |f x y - g x y| ≤ M / min (1 - p₁) (1 - p₂) := by sorry

end BellmanDP.GoldMining
