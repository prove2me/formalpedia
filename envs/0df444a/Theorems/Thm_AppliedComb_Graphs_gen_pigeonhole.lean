-- Prove2me | Theorems.Thm_AppliedComb_Graphs_gen_pigeonhole
-- name    : AppliedComb.Graphs.gen_pigeonhole
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:03:29.581394+00:00
-- url     : https://prove2.me/theorems/aa64c45b-2d87-42cc-a248-e4a34925ee04
-- title:
--   Proposition 5.24 — Generalized Pigeon Hole Principle
-- statement:
--   Let $X$ and $Y$ be finite sets, $f : X \to Y$ a function and $m$ a natural number with
--   $$|X| \ge (m-1)\,|Y| + 1.$$
--   Then there are an element $y \in Y$ and distinct elements $x_1, \dots, x_m \in X$ with $f(x_i) = y$ for $i = 1, \dots, m$.
--
--   The book uses this to force a monochromatic $n_t$-element subset in the Kelly–Kelly construction behind Proposition 5.25.
--
--   **Formalization Note.** The bound is computed in $\mathbb Z$, so $m - 1$ is not truncated at $m = 0$. The distinct elements are an injective map $x : \{0, \dots, m-1\} \to X$ (`Fin m → X`).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 85, Proposition 5.24

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 85, Proposition 5.24 (Generalized Pigeon Hole Principle). If
`f : X → Y` is a function between finite sets and `|X| ≥ (m − 1)|Y| + 1`, then there exist an
element `y ∈ Y` and distinct elements `x₁, …, x_m ∈ X` with `f(xᵢ) = y` for `i = 1, …, m`.
The bound is computed in `ℤ`, so `m − 1` is not truncated. -/
theorem gen_pigeonhole {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) (m : ℕ)
    (h : ((m : ℤ) - 1) * (Fintype.card Y : ℤ) + 1 ≤ (Fintype.card X : ℤ)) :
    ∃ y : Y, ∃ x : Fin m → X, Function.Injective x ∧ ∀ i : Fin m, f (x i) = y := by sorry

end AppliedComb.Graphs
