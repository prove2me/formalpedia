-- Prove2me | Theorems.Thm_BellmanDP_GoldMining_index_rule_two_mines
-- name    : BellmanDP.GoldMining.index_rule_two_mines
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:13:48.84602+00:00
-- url     : https://prove2.me/theorems/9eedc4dd-09be-443d-a741-cbb169bcc830
-- title:
--   Chapter II, Theorem 2 — the index rule $p_1r_1x/(1-p_1)\gtrless p_2r_2y/(1-p_2)$ for two mines
-- statement:
--   Let $0 \le p_1, p_2 < 1$ and $0 \le r_1, r_2 \le 1$, and let $f$ be the solution of the gold-mining equation
--   $$f(x,y) = \max\Bigl[A: p_1\bigl(r_1x + f((1-r_1)x,\,y)\bigr),\; B: p_2\bigl(r_2y + f(x,\,(1-r_2)y)\bigr)\Bigr], \qquad x, y \ge 0,$$
--   that is, a solution bounded in every rectangle $0 \le x \le \bar X$, $0 \le y \le \bar Y$. Then at every point $x, y \ge 0$:
--   1. if $\dfrac{p_1r_1x}{1-p_1} > \dfrac{p_2r_2y}{1-p_2}$, then $f(x,y)$ equals the A-branch;
--   2. if $\dfrac{p_1r_1x}{1-p_1} < \dfrac{p_2r_2y}{1-p_2}$, then $f(x,y)$ equals the B-branch;
--   3. if $\dfrac{p_1r_1x}{1-p_1} = \dfrac{p_2r_2y}{1-p_2}$, then $f(x,y)$ equals both branches: either choice is optimal.
--
--   Bellman reads the rule as maximizing the ratio of immediate expected gain $p_ir_i\cdot(\text{gold})$ to immediate expected loss $1-p_i$.
--
--   **Formalization Note** The book's class ("bounded in any rectangle") is a hypothesis on $f$; Theorem 1 gives existence for $r_i < 1$, and the same successive-approximation argument gives it for $r_i = 1$, so the statement is not vacuous on the book's wider range $0 \le r_i \le 1$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter II, § 8, Theorem 2, p. 69

import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 2, p. 69: for `0 ≤ p₁, p₂ < 1`,
`0 ≤ r₁, r₂ ≤ 1`, the solution `f` of (9) (the solution bounded in every rectangle) satisfies, at
every `x, y ≥ 0`: `f = A`-branch when `p₁ r₁ x/(1 − p₁) > p₂ r₂ y/(1 − p₂)`, `f = B`-branch when
the reverse strict inequality holds, and both branches equal `f` (either choice is optimal) on
equality. -/
theorem index_rule_two_mines (p₁ p₂ r₁ r₂ : ℝ)
    (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ < 1) (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ < 1)
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf : IsGoldMiningSolution p₁ p₂ r₁ r₂ f) (hfb : BoundedOnRectangles f)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (p₂ * r₂ * y / (1 - p₂) < p₁ * r₁ * x / (1 - p₁) → f x y = goldA p₁ r₁ f x y) ∧
    (p₁ * r₁ * x / (1 - p₁) < p₂ * r₂ * y / (1 - p₂) → f x y = goldB p₂ r₂ f x y) ∧
    (p₁ * r₁ * x / (1 - p₁) = p₂ * r₂ * y / (1 - p₂) →
      f x y = goldA p₁ r₁ f x y ∧ f x y = goldB p₂ r₂ f x y) := by sorry

end BellmanDP.GoldMining
