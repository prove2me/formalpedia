-- Prove2me | Theorems.Thm_Arxiv1909_04681_besselI4_from_I0_I1
-- name    : Arxiv1909_04681.besselI4_from_I0_I1
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:49:55.251384+00:00
-- url     : https://prove2.me/theorems/c5e4f70e-84e4-4f5f-ab2e-99ab620d1006
-- title:
--   Eqs. (37)-(40): $I_4$ in terms of $I_0$ and $I_1$
-- statement:
--   Let $I_n$ be the modified Bessel functions of the first kind and $C_{j,n}$ the coefficient of $z^j$ in the series of $I_n$ (eqs. 34-36).
--
--   1. (Eq. 37.) $C_{4,4}=\frac1{384}$, $C_{6,4}=\frac1{7680}$, $C_{8,4}=\frac1{368640}$, $C_{10,4}=\frac1{30965760}$, and for every real $z$, $I_4(z)=\sum_{k\ge0}C_{4+2k,4}\,z^{4+2k}$.
--   2. (System after eq. 38.) Real numbers $A,B,C,D$ make the coefficients of $z^{-2},z^0,z^2,z^4$ in $\tilde I_4(z)=A\,I_0(z)+B\,I_1(z)/z+C\,I_0(z)/z^2+D\,I_1(z)/z^3$ equal those of $I_4$, that is $$A\,C_{j,0}+B\,C_{j+1,1}+C\,C_{j+2,0}+D\,C_{j+3,1}=C_{j,4}\qquad(j=-2,0,2,4),$$ if and only if $(A,B,C,D)=(1,-8,24,-48)$.
--   3. (Eq. 39.) With these values the coefficients agree at every order: $C_{j,0}-8C_{j+1,1}+24C_{j+2,0}-48C_{j+3,1}=C_{j,4}$ for every integer $j$.
--   4. (Eq. 40.) For every $z>0$, $$I_4(z)=I_0(z)-8\frac{I_1(z)}{z}+24\frac{I_0(z)}{z^2}-48\frac{I_1(z)}{z^3}.$$
--
--   This lets $I_4$ be computed from $I_0$ and $I_1$ alone.
--
--   **Formalization Note** For $j=-2,0,2,4$ the four matching conditions are exactly the four printed linear equations $C+D/2=0$, $A+B/2+C/4+D/16=0$, $A/4+B/16+C/64+D/384=0$, $A/64+B/384+C/2304+D/18432=1/384$. The paper calls eq. (40) an approximation "up to arbitrary order" that becomes an equality when the expansion is taken to infinite order; the statement is that equality. $z=\kappa$ is a concentration parameter, hence $z>0$.
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c017; Appendix B, eqs. (35)-(40) and the system of equations between (38) and (39), PDF pp. 9-10

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem besselI4_from_I0_I1 :
    (besselCoeff 4 4 = 1 / 384 ∧ besselCoeff 6 4 = 1 / 7680 ∧
      besselCoeff 8 4 = 1 / 368640 ∧ besselCoeff 10 4 = 1 / 30965760) ∧
    (∀ z : ℝ, HasSum (fun k : ℕ => besselCoeff (4 + 2 * k) 4 * z ^ (4 + 2 * k)) (besselI 4 z)) ∧
    (∀ A B C D : ℝ,
      (∀ j ∈ ({-2, 0, 2, 4} : Finset ℤ),
        A * besselCoeff j 0 + B * besselCoeff (j + 1) 1 + C * besselCoeff (j + 2) 0 +
          D * besselCoeff (j + 3) 1 = besselCoeff j 4) ↔
      (A = 1 ∧ B = -8 ∧ C = 24 ∧ D = -48)) ∧
    (∀ j : ℤ, 1 * besselCoeff j 0 + (-8) * besselCoeff (j + 1) 1 + 24 * besselCoeff (j + 2) 0 +
        (-48) * besselCoeff (j + 3) 1 = besselCoeff j 4) ∧
    (∀ z : ℝ, 0 < z → besselI 4 z = besselI4Tilde 1 (-8) 24 (-48) z) := by sorry

end Arxiv1909_04681
