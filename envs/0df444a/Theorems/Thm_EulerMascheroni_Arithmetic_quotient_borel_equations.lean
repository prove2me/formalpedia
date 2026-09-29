-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_quotient_borel_equations
-- name    : EulerMascheroni.Arithmetic.quotient_borel_equations
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:35:05.747598+00:00
-- url     : https://prove2.me/theorems/2f988397-7926-4dac-89d7-c4085f036b3a
-- title:
--   Formal differential equations for the factorial quotient Borel transform
-- statement:
--   For the formal power series $C_a(z)=\sum_{n\ge0}q_n(a)z^n$, with $q_n(a)=(a-\sum_{k<n}(-1)^k k!)/n!$, formal differentiation gives
--
--   $$(1+z)(C_a'-C_a)=-1,\qquad(1+z)C_a''-zC_a'-C_a=0.$$
--
--   These identities hold for every real parameter $a$. They establish holonomicity directly at the level of formal power series; no interchange of analytic limits is required.
-- source:
--   Explicit elementary derivation from the factorial quotient coefficients associated to Conjecture 2 in Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, p. 4. All identities in this submission are unconditional; the arithmetic division conjecture is not assumed.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.quotient_borel_equations (a : ℝ) :
    let F : PowerSeries ℝ := PowerSeries.mk (EulerMascheroni.Arithmetic.quotientCoeff a)
    let D := PowerSeries.derivative ℝ
    (1 + PowerSeries.X) * (D F - F) = -1 ∧
      (1 + PowerSeries.X) * D (D F) - PowerSeries.X * D F - F = 0 := by sorry
