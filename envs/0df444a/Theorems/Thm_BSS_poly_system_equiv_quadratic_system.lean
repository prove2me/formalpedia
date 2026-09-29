-- Prove2me | Theorems.Thm_BSS_poly_system_equiv_quadratic_system
-- name    : BSS.poly_system_equiv_quadratic_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T14:59:31.461964+00:00
-- url     : https://prove2.me/theorems/068facba-6577-4daa-b290-ffdfe144a3a7
-- title:
--   §4 Prop. 1(a): every real polynomial system is equivalent to a quadratic system
-- statement:
--   Proposition 1(a) of §4 (p. 20): over the real numbers, any system of polynomial equations is
--   equivalent to a quadratic system. Following the paper's proof, one introduces a new variable
--   $t_\alpha$ for each monomial $x^\alpha$ and the relations $t_{\alpha + \beta} = t_\alpha t_\beta$,
--   which are quadratic, together with the linear equations $\sum_\alpha a_\alpha t_\alpha = 0$.
--
--   The statement records the equivalence in the form the later sections use: the new system lives on
--   at least as many variables, every solution of the original extends to a solution of the quadratic
--   system agreeing with it on the original variables, and every solution of the quadratic system
--   restricts to a solution of the original.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §4, p. 20, Proposition 1(a)

import Mathlib

namespace BSS

theorem poly_system_equiv_quadratic_system {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ) :
    ∃ (N k : ℕ) (hn : n ≤ N) (q : Fin k → MvPolynomial (Fin N) ℝ),
      (∀ j, (q j).totalDegree ≤ 2) ∧
      (∀ x : Fin n → ℝ, (∀ i, MvPolynomial.eval x (p i) = 0) →
          ∃ z : Fin N → ℝ, (∀ i : Fin n, z (Fin.castLE hn i) = x i) ∧
            ∀ j, MvPolynomial.eval z (q j) = 0) ∧
      (∀ z : Fin N → ℝ, (∀ j, MvPolynomial.eval z (q j) = 0) →
          ∀ i, MvPolynomial.eval (fun t : Fin n => z (Fin.castLE hn t)) (p i) = 0) := by sorry

end BSS
