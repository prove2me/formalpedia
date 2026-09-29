-- Prove2me | Theorems.Thm_DiazModulus_no_first_order_arithmetic_operator
-- name    : DiazModulus.no_first_order_arithmetic_operator
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-19T18:41:29.87397+00:00
-- url     : https://prove2.me/theorems/5cd9032c-01c2-4fe8-83cd-02c3f4028f9b
-- title:
--   No first-order arithmetic differential operator for the exponential system of a candidate
-- statement:
--   **No first-order arithmetic differential operator.**
--
--   Let $u$ be a candidate: $u \neq 0$, with $|u|$ and $\mathrm{e}^{u}$ both algebraic. Let
--   $F(z,w) = \exp(u z + \overline{u} w)$ and let $X = a \partial_z + b \partial_w$ be a first-order
--   operator whose coefficients $a, b$ are polynomials with algebraic coefficients. If $(XF)(m,n)$ is
--   algebraic at every lattice point $(m,n) \in \mathbb{Z}^2$, then $a = b = 0$.
--
--   **What it means.** $(XF)(m,n) = \bigl(a(m,n)u + b(m,n)\overline{u}\bigr)F(m,n)$, and $F(m,n)$ is a
--   non-zero algebraic number, so the bracket is algebraic. For a candidate $u$ and $\overline{u}$ are
--   $\mathbb{Q}$-linearly independent logarithms of algebraic numbers, so by Baker's theorem a non-zero
--   algebraic combination of them is transcendental: the bracket vanishes, and it vanishes at every
--   point of $\mathbb{Z}^2$, which forces the coefficient polynomials to be zero.
--
--   The consequence is that the Schneider-Lang criterion, which wants the derivatives of the functions
--   to stay in a ring generated over a number field, has no input here: no operator of order one has
--   algebraic values on the lattice, while $\partial_z \partial_w$ does — and that is not a derivation.
--   Order zero is algebraic trivially, $F$ itself being algebraic at lattice points.
--
--   **Role.** One of the two obstructions to running a classical interpolation argument on a candidate.
--   The other is that the interpolation matrix factors as a Kronecker product
--   (`DiazModulus.kronecker_factorisation`), so its determinant sees none of the candidate's arithmetic.
--
--   **Honesty about its shape.** The hypothesis class is conjecturally empty. Diaz's conjecture asserts
--   that no candidate exists, so this is a statement about a hypothetical counterexample. Nothing here
--   asserts that a candidate exists.
--
--   **Hypotheses.** Baker's theorem is not available in this environment, so it is **carried as an
--   explicit hypothesis**, `hbaker`, in exactly the form the proof consumes: an algebraic combination of
--   $u$ and $\overline{u}$ that is algebraic has both coefficients zero. For a candidate that is Baker's
--   theorem applied to two $\mathbb{Q}$-independent logarithms; the independence is
--   `Diaz.indep_of_not_axis` (Proved). Of the candidate hypothesis the proof consumes only that
--   $\mathrm{e}^{u}$ is algebraic.
--
--   **Narrower than the rational case, deliberately.** Proposition 5.9 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9) states the polynomial case, as the node does, and remarks that the same holds for $a, b$ rational
--   functions with algebraic coefficients, regular on $\mathbb{Z}^2$. The rational case follows by clearing denominators, and that step is not formalised here.
--
--   **Novelty.** The argument is Baker's theorem plus the fact that a polynomial vanishing
--   on $\mathbb{Z}^2$ is zero. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 5.9. Background: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000 (the Schneider-Lang criterion and Schwarz' lemma for Cartesian products); G. Diaz, J. Theor. Nombres Bordeaux 19 (2007), 373-391.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem no_first_order_arithmetic_operator
    (u : ℂ) (hu : IsCandidate u)
    (hbaker : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
        IsAlgebraic ℚ (p * u + q * conj u) → p = 0 ∧ q = 0)
    (a b : MvPolynomial (Fin 2) ℂ)
    (ha : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d a))
    (hb : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d b))
    (hvalues : ∀ m n : ℤ,
        IsAlgebraic ℚ
          ((MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a * u
              + MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b * conj u)
            * Complex.exp (u * m + conj u * n))) :
    a = 0 ∧ b = 0 := by sorry

end DiazModulus
