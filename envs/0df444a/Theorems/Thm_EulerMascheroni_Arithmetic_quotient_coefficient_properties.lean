-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_quotient_coefficient_properties
-- name    : EulerMascheroni.Arithmetic.quotient_coefficient_properties
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:34:57.441287+00:00
-- url     : https://prove2.me/theorems/3e789719-4706-4a7c-ac9a-4d6ce5bdd644
-- title:
--   Recurrence, growth, and algebraicity of factorial quotient coefficients
-- statement:
--   For $a\in\mathbb R$, let $q_n(a)=(a-\sum_{k<n}(-1)^k k!)/n!$. Then
--
--   $$q_0(a)=a,\qquad(n+1)q_{n+1}(a)=q_n(a)-(-1)^n,\qquad |q_n(a)|\le|a|+1.$$
--
--   If $a$ is algebraic, every $q_n(a)$ is algebraic. These unconditional identities establish the elementary coefficient properties needed to study the Borel transform. They impose no common-denominator bound.
-- source:
--   Explicit elementary derivation from the factorial quotient coefficients associated to Conjecture 2 in Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, p. 4. All identities in this submission are unconditional; the arithmetic division conjecture is not assumed.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.quotient_coefficient_properties (a : ℝ) :
    EulerMascheroni.Arithmetic.quotientCoeff a 0 = a ∧
    ∀ n : ℕ,
      (((n+1 : ℕ) : ℝ) * EulerMascheroni.Arithmetic.quotientCoeff a (n+1) =
        EulerMascheroni.Arithmetic.quotientCoeff a n - (-1 : ℝ)^n) ∧
      |EulerMascheroni.Arithmetic.quotientCoeff a n| ≤ |a| + 1 ∧
      (IsAlgebraic ℚ a → IsAlgebraic ℚ (EulerMascheroni.Arithmetic.quotientCoeff a n)) := by sorry
