-- Prove2me | Theorems.Thm_BellmanDP_Games_survival_game_exists_unique
-- name    : BellmanDP.Games.survival_game_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T20:56:04.441214+00:00
-- url     : https://prove2.me/theorems/99b87d40-d302-4b45-8c10-e49a24d60143
-- title:
--   Chapter X, Theorem 5 — existence and uniqueness for games of survival
-- statement:
--   A game of survival is a generalized gambler's ruin. Player $A$ holds an integer amount $x$ of a fixed total, and at each stage the two players play the $2\times 2$ matrix game
--   $$A=\begin{pmatrix}-1 & a\\ c & -b\end{pmatrix},$$
--   where $a,b,c$ are positive integers with $a>1$. The entry is the amount transferred to $A$. $A$ is ruined at $x\le 0$ and wins at $x\ge d$, where $d\ge1$ is an integer. Consider the equation
--   $$f(x)=\min_q\max_p\big[p_1q_1f(x-1)+p_1q_2f(x+a)+p_2q_1f(x+c)+p_2q_2f(x-b)\big]=\max_p\min_q\big[\ \cdots\ \big]$$
--   for $x=1,2,\dots,d-1$, where $p=(p_1,p_2)$ and $q=(q_1,q_2)$ range over distribution vectors, with the boundary conditions
--   $$f(x)=0\quad(x\le 0),\qquad f(x)=1\quad(x\ge d).$$
--   Then there is a unique function $f:\mathbb Z\to\mathbb R$ satisfying $0\le f(x)\le 1$ for all $x$ that satisfies the equation and the boundary conditions.
--
--   Here $f(x)$ is the probability that $A$ ruins $B$ under optimal play. The theorem shows the functional equation of the game determines it.
--
--   **Formalization Note** The condition $d\ge 1$ is implicit in the book: for $d\le0$ the two boundary conditions contradict each other. Distribution vectors are points of the standard simplex on two points, and the equation asserts that both extrema are attained and equal $f(x)$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter X, § 19, Theorem 5, p. 303

import Mathlib
import Definitions.Def_BellmanDP_Games_MinMax

namespace BellmanDP.Games

/-- Bellman, *Dynamic Programming*, Ch. X, Theorem 5, p. 303 (existence and uniqueness for games
of survival). Let `a, b, c` be positive integers with `a > 1`, and `d ≥ 1` an integer. There is a
unique function `f : ℤ → ℝ` with `0 ≤ f(x) ≤ 1` for all `x` that satisfies the boundary conditions
`f(x) = 0` for `x ≤ 0`, `f(x) = 1` for `x ≥ d` (19.3), and, for `x = 1, 2, …, d − 1`, the
equation (19.1)
`f(x) = Min_q Max_p [p₁q₁ f(x−1) + p₁q₂ f(x+a) + p₂q₁ f(x+c) + p₂q₂ f(x−b)] = Max_p Min_q [⋯]`,
over distribution vectors `p, q` on two points. -/
theorem survival_game_exists_unique (a b c d : ℤ) (ha : 1 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 1 ≤ d) :
    ∃! f : ℤ → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x, x ≤ 0 → f x = 0) ∧ (∀ x, d ≤ x → f x = 1) ∧
      ∀ x, 1 ≤ x → x ≤ d - 1 →
        IsMaxMinMinMaxValue (survivalPayoff a b c f x) (stdSimplex ℝ (Fin 2))
          (stdSimplex ℝ (Fin 2)) (f x) := by sorry

end BellmanDP.Games
