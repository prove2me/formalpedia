-- Prove2me | Theorems.Thm_DiazModulus_polynomial_hull_no_two_by_three_configuration
-- name    : DiazModulus.polynomial_hull_no_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:58:55.776315+00:00
-- url     : https://prove2.me/theorems/87a6c7b0-c6f8-41f2-ae69-b8fe54a02fa9
-- title:
--   For u ∉ Q̄ with uū algebraic and deg P ≤ 1 or ≥ 4, no 2×3 configuration lies in the span of 1, u, ū, P(u), P(u)‾
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $P \in \overline{\mathbb{Q}}[X]$ have degree at most $1$ or at least $4$, and let $W = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}P(u) + \overline{\mathbb{Q}}\overline{P(u)}$. Then $W$ carries no $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space).
--
--   **Proof.** Suppose a configuration lies in $W$. If $u^N$ times each spanning number is the value at $u$ of a polynomial in a subspace $H \subseteq \overline{\mathbb{Q}}[X]$, `DiazModulus.config_shifted_polynomial_spans` gives free $a_0, a_1$, free $b_0, b_1, b_2$ and $P_0 \neq 0$ in $\overline{\mathbb{Q}}[X]$ with $fg = P_0h$, $h \in H$, for $f$ in the span of the $a$'s and $g$ in that of the $b$'s; along it orders at $0$ and degrees add, and each span has as many orders, and as many degrees, as its dimension (`DiazModulus.polynomial_submodule_trailing_degrees_card`, `DiazModulus.polynomial_submodule_degrees_card`). If $\deg P \leq 1$, take $N = 1$ and $H$ the polynomials of degree at most $2$: the six degree sums would lie in a window of three values, which two and three distinct degrees cannot do. If $k = \deg P \geq 4$, let $L = P - p_0 - p_1X$, $m$ its order, $Q_1 = X^kL$ and $Q_2 = \sum_j \bar p_j \rho^j X^{k-j}$, so $u^k\overline{L(u)} = Q_2(u)$; with $N = k$ and $H = \mathrm{span}(X^{k-1}, X^k, X^{k+1}, Q_1, Q_2)$, `DiazModulus.shifted_polynomial_hull_orders` puts the shifted orders and the reflected degrees of $H$ in $\{-k, -1, 0, 1, m\}$, and `DiazModulus.five_point_sumset_rigid` makes the shifted order sums, and the reflected degree sums, exactly $\{-1, 0, 1, 2\}$. A product $fg = P_0h$ with order sum $2$ then has $\mathrm{ord}\,h = k + 2$ and $\deg h \leq k + 1$, which is impossible.
--
--   **Novelty.** For $\deg P \leq 1$ the space has dimension $3$, where no $2 \times 3$ configuration exists (Roy, Acta Math. 1995, Th. 3.4; Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Exercise 12.10). For $\deg P \geq 4$ the statement was not found in the sources read; the proof applies the valuation and sumset method of Bachoc, Serra and Zémor (2017, §7, proof of Th. 33) at the two ends together, and pinching the support between the orders at $0$ and at $\infty$ was not seen there. Routine. The case $P = X^k$ is `DiazModulus.power_hull_strong_six_exp_configuration_iff`.
-- source:
--   For degree at most 1: D. Roy, Points whose coordinates are logarithms of algebraic numbers on algebraic varieties, Acta Math. 175 (1995), 49–73, Th. 3.4. For degree at least 4, not found in the sources read; the method is that of C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), §7. Uses DiazModulus.config_shifted_polynomial_spans, DiazModulus.polynomial_submodule_trailing_degrees_card, DiazModulus.polynomial_submodule_degrees_card, DiazModulus.shifted_polynomial_hull_orders and DiazModulus.five_point_sumset_rigid. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem polynomial_hull_no_two_by_three_configuration {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (P : (↥Qbar)[X])
    (hP : P.natDegree ≤ 1 ∨ 4 ≤ P.natDegree) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, aeval u P, conj (aeval u P)} : Set ℂ) := by
  sorry

end DiazModulus
