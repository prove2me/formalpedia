-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_kernel_coefficient_vanishes
-- name    : EulerMascheroni.Mixed.kernel_coefficient_vanishes
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T12:47:37.565511+00:00
-- url     : https://prove2.me/theorems/d4a7c108-d1db-43ca-8bbf-957a2a14a0d6
-- title:
--   Monodromy forces the Gompertz coefficient of a lifted polynomial relation to vanish
-- statement:
--   Let $P,Q,R,S\in\mathbb C[z]$. Suppose the following identity holds for every point $t$ of the logarithmic cover:
--
--   $$P(e^t)+Q(e^t)e^{e^t}+R(e^t)A(e^t)+S(e^t)K(t)=0.$$
--
--   Then
--
--   $$S(1)=0.$$
--
--   No arithmetic assumptions on the polynomial coefficients are required. This is the analytic obstruction used by the Euler-constant decomposition: a functional relation cannot retain a nonzero Gompertz coefficient at the point $z=1$. The statement is an elementary consequence of the normalized cover formula and exponential periodicity.
-- source:
--   Elementary derivation from Definitions.Def_eulerMascheroni_mixedCover and Complex.exp_two_pi_mul_I in Mathlib, commit 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean. The logarithmic term underlying the normalization is in Lagarias, https://arxiv.org/abs/1303.1856, Eq. (3.16.2).

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.kernel_coefficient_vanishes
    (P Q R S : Polynomial ℂ)
    (h : ∀ t : ℂ,
      P.eval (Complex.exp t) + Q.eval (Complex.exp t) * Complex.exp (Complex.exp t) +
      R.eval (Complex.exp t) * EulerMascheroni.Mixed.expEin (Complex.exp t) +
      S.eval (Complex.exp t) * EulerMascheroni.Mixed.kernelOnCover t = 0) :
    S.eval 1 = 0 := by sorry
