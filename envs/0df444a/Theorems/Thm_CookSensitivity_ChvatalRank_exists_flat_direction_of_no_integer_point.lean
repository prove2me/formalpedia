-- Prove2me | Theorems.Thm_CookSensitivity_ChvatalRank_exists_flat_direction_of_no_integer_point
-- name    : CookSensitivity.ChvatalRank.exists_flat_direction_of_no_integer_point
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T07:00:32.209078+00:00
-- url     : https://prove2.me/theorems/fd3de340-3f31-4016-a640-0bf2d27fd25f
-- title:
--   Flatness theorem (Lenstra; Grötschel–Lovász–Schrijver) — a lattice-free rational polyhedron has width $\le n(n+1)2^{n^2/2}$ in some integral direction
-- statement:
--   This is the flatness theorem for lattice-free rational polyhedra, in the form used by Cook, Gerards, Schrijver and Tardos.
--
--   Let $n \ge 1$ and let $P = \{x \in \mathbb{Q}^n : Dx \le d\}$ be a rational polyhedron (possibly unbounded, possibly empty) that contains no integral vector, $P \cap \mathbb{Z}^n = \emptyset$. Then there is a nonzero integral vector $w \in \mathbb{Z}^n$ such that
--
--   $$|w(x - x')| \;\le\; n(n+1)\,2^{\frac12 n^2} \qquad \text{for all } x, x' \in P.$$
--
--   In words: a lattice-free rational polyhedron is *flat* in some integral direction $w$ — its lattice width in direction $w$ is bounded by a number depending only on the dimension. For bounded $P$ the existence of such a direction is due to Lenstra; the version for arbitrary rational polyhedra, with this bound, is due to Grötschel, Lovász and Schrijver. It is the geometric input to the proof of the Cook–Coullard–Turán theorem that lattice-free polyhedra have Chvátal rank at most $n^{2n}2^{n^3}$: one cuts the polyhedron down along the flat direction $w$, one hyperplane $wx = \beta$ at a time, using induction on the dimension on each hyperplane.
--
--   **Formalization Note** Points are `Fin n → ℚ` and "polyhedron" is `IsPolyhedron` (finitely many rational inequalities). The hypothesis $n \ge 1$ is needed because $\mathbb{Z}^0$ has no nonzero vector (in dimension $0$ every lattice-free polyhedron is empty anyway). The width $w(x-x')$ is computed in $\mathbb{Q}$ and compared in $\mathbb{R}$ with the bound $n(n+1)\cdot 2^{n^2/2}$, where the power is the real power `Real.rpow`. The paper prints the inequality as strict in one place; the non-strict form stated here is the weaker one and is all that the proof of Theorem 8 uses.
-- source:
--   Cook, Gerards, Schrijver, Tardos, Sensitivity theorems in integer linear programming, Math. Programming 34 (1986), p. 259, proof of Theorem 9 [cited as Theorem 8], citing Grötschel, Lovász, Schrijver [18] (Geometric Algorithms and Combinatorial Optimization, Springer 1988) and, for bounded P, Lenstra [22] (Integer programming with a fixed number of variables, Math. Oper. Res. 8 (1983))

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace CookSensitivity.ChvatalRank

open Matrix

theorem exists_flat_direction_of_no_integer_point {n : ℕ} (hn : 1 ≤ n) (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∀ x ∈ P, ¬ IsIntegral x) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ ∀ x ∈ P, ∀ x' ∈ P,
      |((((fun i => (w i : ℚ)) ⬝ᵥ (x - x') : ℚ)) : ℝ)| ≤
        ((n * (n + 1) : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) ^ 2 / 2) := by sorry

end CookSensitivity.ChvatalRank
