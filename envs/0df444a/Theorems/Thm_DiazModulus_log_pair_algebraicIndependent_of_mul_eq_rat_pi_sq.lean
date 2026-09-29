-- Prove2me | Theorems.Thm_DiazModulus_log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq
-- name    : DiazModulus.log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T18:03:01.112283+00:00
-- url     : https://prove2.me/theorems/1f17c4b6-9163-42b2-bf17-fd14a9cd9448
-- title:
--   Two logarithms whose product is a rational multiple of π² are algebraically independent (Diaz 1997, Proposition 1)
-- statement:
--   Let $\ell_1, \ell_2$ be logarithms of algebraic numbers, that is $e^{\ell_1}, e^{\ell_2} \in \overline{\mathbb Q}$, and assume that $e^{\ell_1}$ is not a root of unity, i.e. $\ell_1 \notin 2\pi i\,\mathbb Q$. If
--
--   $$\ell_1\,\ell_2 = c\,\pi^2$$
--
--   for a non-zero rational number $c$, then $\ell_1$ and $\ell_2$ are algebraically independent over $\mathbb Q$, and so are $\ell_1$ and $2\pi i$.
--
--   This is Proposition 1 of Diaz (1997), whose hypothesis is that $\ell_1\ell_2$ and $\pi^2$ are linearly dependent over $\mathbb Q$. The proof applies the four exponentials theorem in transcendence degree one (`DiazModulus.four_exponentials_trdeg_one`) to the matrix
--
--   $$\begin{pmatrix} \ell_1 & -\tfrac{c}{4}\,2\pi i \\ 2\pi i & \ell_2 \end{pmatrix},$$
--
--   whose determinant vanishes because $(2\pi i)^2 = -4\pi^2$.
-- source:
--   Known: G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, Proposition 1. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq (l₁ l₂ : ℂ)
    (h₁ : IsAlgebraic ℚ (Complex.exp l₁)) (h₂ : IsAlgebraic ℚ (Complex.exp l₂))
    (hroot : ∀ q : ℚ, l₁ ≠ (q : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
    (c : ℚ) (hc : c ≠ 0) (hprod : l₁ * l₂ = (c : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) :
    AlgebraicIndependent ℚ ![l₁, l₂] ∧
      AlgebraicIndependent ℚ ![l₁, 2 * ((Real.pi : ℝ) : ℂ) * Complex.I] := by
  sorry

end DiazModulus
