-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_factorial_division_denominators_conjecture
-- name    : EulerMascheroni.Arithmetic.factorial_division_denominators_conjecture
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T13:19:14.854589+00:00
-- url     : https://prove2.me/theorems/241c0c17-9b21-43a9-8e8c-f97625cb4a57
-- title:
--   Conjectural arithmetic division bounds for the Gompertz factorial quotient
-- statement:
--   **Conjectural arithmetic division step; no proof is asserted.** Suppose the Gompertz constant $\delta$ is algebraic, and set
--
--   $$q_n(\delta)=\frac{\delta-\sum_{k=0}^{n-1}(-1)^k k!}{n!}.$$
--
--   The proposed conclusion is that there is $C\ge1$ such that each initial segment has a common positive integer denominator $D_n\le C^{n+1}$ in the ring of algebraic integers:
--
--   $$D_nq_k(\delta)\in\overline{\mathbb Z}\qquad(0\le k\le n).$$
--
--   This is a specific consequence of the conjectural division theorem for arithmetic Gevrey series whose Borel sum vanishes at an algebraic point. It concerns arithmetic denominators, not just analytic convergence. In combination with the unconditional denominator obstruction it implies Gompertz transcendence, so it is not presented as a weaker solved estimate.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, p. 4. Specialize to the formal series f(w)=delta−sum_{n≥0} (−1)^n n! w^{n+1}, assuming delta algebraic. Its positive-direction Borel sum vanishes at w=1. The coefficients of f(w)/(1−w) are delta−sum_{k<n}(−1)^k k!. The G-function condition on the Borel transform gives exactly the proposed denominator bound. This is a conditional specialization, not a result proved in the source.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.factorial_division_denominators_conjecture
    (h : IsAlgebraic ℚ EulerMascheroni.gompertzConstant) :
    EulerMascheroni.Arithmetic.ExponentialDenominators EulerMascheroni.gompertzConstant := by sorry
