-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_mixed_value_coefficient_sum
-- name    : EulerMascheroni.Mixed.mixed_value_coefficient_sum
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T14:22:46.048794+00:00
-- url     : https://prove2.me/theorems/98a3ba1d-9d97-4728-bc74-972b5396b848
-- title:
--   Summation and initial coefficient of the mixed E-value Taylor series
-- statement:
--   For the Taylor coefficients $f_n(a,b,c)$ of $a+b e^z+c e^z\operatorname{Ein}(z)$,
--
--   $$\sum_{n\ge0}f_n(a,b,c)=a+b e+c e\operatorname{Ein}(1),\qquad f_0(a,b,c)=a+b.$$
--
--   This is an unconditional convergent-series statement. It supplies the analytic input for applying the arithmetic quotient boundary lemma.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjectures 1–3, Lemma 2(ii), and §4.3. The coefficient formulation here is derived explicitly for this decomposition; it is not claimed to be a newly proved intersection theorem.

import Definitions.Def_eulerMascheroni_mixedCoefficients
open EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.mixed_value_coefficient_sum (a b c : ℝ) :
    HasSum (EulerMascheroni.Mixed.valueCoefficient a b c)
      ((a:ℂ)+(b:ℂ)*Complex.exp 1+(c:ℂ)*EulerMascheroni.Mixed.expEin 1) ∧
    EulerMascheroni.Mixed.valueCoefficient a b c 0 = (a:ℂ)+(b:ℂ) := by sorry
