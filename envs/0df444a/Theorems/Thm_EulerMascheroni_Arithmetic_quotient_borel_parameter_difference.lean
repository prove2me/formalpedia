-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_quotient_borel_parameter_difference
-- name    : EulerMascheroni.Arithmetic.quotient_borel_parameter_difference
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:34:52.118924+00:00
-- url     : https://prove2.me/theorems/0531b63d-f119-4c33-a65c-bf40eac197df
-- title:
--   Changing the Borel boundary coefficient adds an exponential solution
-- statement:
--   Let $C_a(z)=\sum_{n\ge0}(a-\sum_{k<n}(-1)^k k!)z^n/n!$. For all real $a,b$,
--
--   $$C_a(z)-C_b(z)=(a-b)e^z$$
--
--   as formal power series. Thus the free boundary parameter changes only the homogeneous exponential solution. This identifies why selecting an analytic boundary value does not by itself control its arithmetic.
-- source:
--   Explicit elementary derivation from the factorial quotient coefficients associated to Conjecture 2 in Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, p. 4. All identities in this submission are unconditional; the arithmetic division conjecture is not assumed.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.quotient_borel_parameter_difference (a b : ℝ) :
    PowerSeries.mk (EulerMascheroni.Arithmetic.quotientCoeff a) -
      PowerSeries.mk (EulerMascheroni.Arithmetic.quotientCoeff b) =
      PowerSeries.C (a-b) * PowerSeries.exp ℝ := by sorry
