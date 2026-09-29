-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_e_values_linear_independent
-- name    : EulerMascheroni.Mixed.e_values_linear_independent
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T13:19:01.701238+00:00
-- url     : https://prove2.me/theorems/6ccf72e9-9e25-4923-8a8e-a292afb44a06
-- title:
--   Classical algebraic linear independence of 1, e, and e Ein(1)
-- statement:
--   Let $A(z)=e^z\operatorname{Ein}(z)$. For real algebraic numbers $a,b,c$,
--
--   $$a+be+cA(1)=0\quad\Longrightarrow\quad a=b=c=0.$$
--
--   This is an unconditional classical consequence of E-function transcendence theory. The node asks for its formalization; it is not a mathematical conjecture. The values can be taken in the complex numbers without changing the real coefficients.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2(ii), p. 11, and §4.3, p. 15, integer case a=1, s=1. The series there gives E_{1,2}(-1)=Ein(1). Use the unconditional independence argument in §4.3, not its surrounding conjectural hypothesis.

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.e_values_linear_independent
    (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by sorry
