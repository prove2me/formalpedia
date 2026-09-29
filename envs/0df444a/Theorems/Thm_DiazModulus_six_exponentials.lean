-- Prove2me | Theorems.Thm_DiazModulus_six_exponentials
-- name    : DiazModulus.six_exponentials
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:44:59.918939+00:00
-- url     : https://prove2.me/theorems/7d362030-8eff-4aa9-8138-7b9b15cda0be
-- title:
--   The six exponentials theorem
-- statement:
--   **The six exponentials theorem** (Siegel; Lang; Ramachandra). Let $x_1,x_2$ be complex numbers linearly independent over $\mathbb{Q}$, and let $y_1,y_2,y_3$ likewise be linearly independent over $\mathbb{Q}$. Then at least one of the six numbers
--   $$e^{x_iy_j}\qquad (1\le i\le 2,\ 1\le j\le 3)$$
--   is transcendental.
--
--   It belongs in this mission as the **proved** member of the family the conjecture sits in. Diaz's question follows from the *strong four exponentials* conjecture, which is open; the six exponentials theorem is what is actually known in that direction, and the gap between the two — three columns rather than two, and $\mathbb{Q}$-linear independence rather than $\bar{\mathbb{Q}}$-linear independence — measures precisely how far the standard machinery falls short of settling Diaz.
--
--   It is also not in Mathlib. Proving it needs a Schneider--Lang style argument: build an auxiliary function vanishing to high order at the lattice points $x_iy_j$ by Siegel's lemma, bound it by the maximum principle, and force a contradiction from the fact that a non-zero algebraic integer has absolute norm at least one.
--
--   The formalisation states linear independence over $\mathbb{Q}$, which is the classical hypothesis. The corresponding statement with $\bar{\mathbb{Q}}$-linear independence and $2\times 2$ instead of $2\times 3$ is the four exponentials conjecture and is open; do not confuse the two.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley 1966, Chapter 2; K. Ramachandra, Contributions to the theory of transcendental numbers I, Acta Arith. 14 (1968) 65-72; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer 2000, Section 1.3 and Theorem 1.12

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem six_exponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by sorry
end DiazModulus
