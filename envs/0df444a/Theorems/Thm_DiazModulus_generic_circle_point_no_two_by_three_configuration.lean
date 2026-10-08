-- Prove2me | Theorems.Thm_DiazModulus_generic_circle_point_no_two_by_three_configuration
-- name    : DiazModulus.generic_circle_point_no_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:32:55.117591+00:00
-- url     : https://prove2.me/theorems/2f818ada-bb16-408c-9e9d-66186a87e8fb
-- title:
--   For u ≠ 0 with uū algebraic and numbers w₁, …, w_m with (u, w) algebraically independent over Q̄, no rank-one 2×3 configuration has its products in Q̄ + Q̄u + Q̄ū + ΣQ̄w_j
-- statement:
--   Let $u \neq 0$ with $u\bar u$ algebraic, and let $w_1, \dots, w_m$ be complex numbers such that $u, w_1, \dots, w_m$ are algebraically independent over $\overline{\mathbb{Q}}$. Put $E = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \sum_j \overline{\mathbb{Q}}w_j$. Then there are no $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_i y_j$ in $E$.
--
--   For a candidate $u$ and logarithms $w_j$, this says that the strong six exponentials theorem, and any theorem whose hypothesis is a rank-one $2\times 3$ configuration, cannot refute the candidate on generic data, whatever logarithms are added. The case $m = 1$, $w_1 = i\pi$ is `DiazModulus.generic_no_strong_six_exp_configuration`; the case $m = 0$ is a dimension count of Roy. A $2 \times 2$ configuration does exist: $x = (1, u)$, $y = (1, \bar u)$. The exponential of $u$ plays no role, so the statement keeps its content if Diaz's conjecture holds; it applies to any point of a circle of algebraic radius, such as $e^{i}$.
--
--   **Proof.** Multiply by $u$: the six products $u x_i y_j$ lie in $uE$. Since $\bar u = \rho/u$ with $\rho$ algebraic, every element of $uE$ is the value at $(u, w)$ of a polynomial over $\overline{\mathbb{Q}}$ of total degree at most two that becomes constant when the first variable $X_0$ is set to $0$. Evaluation at $(u, w)$ is injective by algebraic independence, so the configuration comes from a rank-one $2 \times 3$ matrix of such polynomials. In the polynomial ring it factors as $(h, g) \otimes (c_0, c_1, c_2)$ with both factors free. Total degrees add, and setting $X_0 = 0$ is a ring map. If $h$ and $g$ both vanish at $X_0 = 0$, they are scalar multiples of $X_0$ unless every $c_j$ is constant. Otherwise every $c_j$ becomes constant at $X_0 = 0$, and the $c_j$ lie in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}X_0$ unless $h$ and $g$ are constant. Each case puts two free vectors in a line or three in a plane, which is impossible.
--
--   **Novelty.** The case $m = 0$ is Roy's (1995, Th. 3.4; DALAG, Lemma 12.16 and Exercise 12.10), and Roy (1995, §3.2) and Fischler (2001, p. 186) explain why rank methods cannot reach Diaz's conjecture. The statement with any number of auxiliary numbers was not found in the sources read.
-- source:
--   Generalises the case m = 0 (D. Roy, Points whose coordinates are logarithms of algebraic numbers on algebraic varieties, Acta Math. 175 (1995), 49–73, Th. 3.4; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 12.16 and Ex. 12.10) and DiazModulus.generic_no_strong_six_exp_configuration (m = 1, w = iπ). Related barriers: D. Roy, Points whose coordinates are logarithms of algebraic numbers on algebraic varieties, Acta Math. 175 (1995), 49–73, §3.2; S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, p. 186. The general statement was not found in the sources read. Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_circle_point_no_two_by_three_configuration (m : ℕ) (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u)) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent (↥Qbar) (Fin.cons u w : Fin (m + 1) → ℂ))
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, conj u} : Set ℂ) ∪ Set.range w) := by
  sorry

end DiazModulus
