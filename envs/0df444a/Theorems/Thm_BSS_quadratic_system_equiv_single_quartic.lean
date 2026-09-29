-- Prove2me | Theorems.Thm_BSS_quadratic_system_equiv_single_quartic
-- name    : BSS.quadratic_system_equiv_single_quartic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T15:03:04.696947+00:00
-- url     : https://prove2.me/theorems/767f4337-9086-4d7b-953a-05448ea473bf
-- title:
--   §4 Prop. 1(b): a quadratic system is equivalent to one equation of degree $\le 4$
-- statement:
--   Proposition 1(b) of §4 (p. 20): over the real numbers, any quadratic system is equivalent to a
--   single equation of degree at most $4$. The paper's proof is to take the sum of the squares.
--
--   Given finitely many polynomials of total degree at most $2$ in $n$ real variables, there is a
--   single polynomial of total degree at most $4$ that vanishes at a point exactly when all of the
--   given polynomials do.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §4, p. 20, Proposition 1(b)

import Mathlib

namespace BSS

theorem quadratic_system_equiv_single_quartic {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ i, (p i).totalDegree ≤ 2) :
    ∃ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ 4 ∧
      ∀ x : Fin n → ℝ,
        (MvPolynomial.eval x f = 0 ↔ ∀ i, MvPolynomial.eval x (p i) = 0) := by sorry

end BSS
