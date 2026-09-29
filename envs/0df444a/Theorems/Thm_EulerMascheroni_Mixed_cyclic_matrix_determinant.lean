-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_cyclic_matrix_determinant
-- name    : EulerMascheroni.Mixed.cyclic_matrix_determinant
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:14:33.126798+00:00
-- url     : https://prove2.me/theorems/03d4d237-c7be-4e29-992e-8ddc36798392
-- title:
--   Explicit cyclic determinant for a linear combination of the Euler E-functions
-- statement:
--   The matrix of the coefficients of $F,F',F''$ in the basis $(1,e^z,e^z\operatorname{Ein}(z))$, for $F=a+be^z+ce^z\operatorname{Ein}(z)$, is
--
--   $$M(z)=\begin{pmatrix}a&b&c\\-c/z&b+c/z&c\\c/z^2-c/z&b+2c/z-c/z^2&c\end{pmatrix}.$$
--
--   Its determinant is $-c^2(az-a+c)/z^2$. At $z=1$ it is $-c^3$, which is nonzero when $c\ne0$. The formal theorem proves these matrix identities; it does not itself assert minimality of a differential operator.
-- source:
--   Explicit consequences of the Euler E-system and factorial-quotient recurrence, derived for this decomposition. Compare Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorems 2.5 and 3.2, and Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, §4.1 and §4.3.

import Mathlib

theorem EulerMascheroni.Mixed.cyclic_matrix_determinant (a b c z : ℂ) (hz : z ≠ 0) :
    Matrix.det (!![a,b,c; -c/z,b+c/z,c; c/z^2-c/z,b+2*c/z-c/z^2,c]) =
      -c^2*(a*z-a+c)/z^2 ∧
    Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) = -c^3 ∧
    (c ≠ 0 → Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) ≠ 0) := by sorry
