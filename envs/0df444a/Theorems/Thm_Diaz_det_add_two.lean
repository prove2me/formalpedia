-- Prove2me | Theorems.Thm_Diaz_det_add_two
-- name    : Diaz.det_add_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:30.374926+00:00
-- url     : https://prove2.me/theorems/47ddec80-bd8c-47cb-a891-32d7f12de9b3
-- title:
--   Polarization of the $2\times2$ determinant: $\det(X+Y)=\det X+\det Y+\operatorname{tr}X\operatorname{tr}Y-\operatorname{tr}(XY)$
-- statement:
--   **The polarization identity for the $2 \times 2$ determinant.**
--
--   For $X, Y$ two $2 \times 2$ matrices over a commutative ring,
--
--   $$\det(X+Y) = \det X + \det Y + \operatorname{tr} X \operatorname{tr} Y - \operatorname{tr}(XY).$$
--
--   **Why.** Expand both sides on the four entries of each matrix.
--
--   **Role.** In Carlo Perassi's proof that the $2\times2$ obstruction is unique, this identity is what turns the determinant of the three-term pencil
--   $x_0 A + x_1 B + x_2 C$ into an explicit ternary quadratic form, whose coefficients can then be matched
--   against $c\,\mathcal{Q}_\rho = c(x_1x_2 - \rho x_0^2)$. That comparison is the mechanism of his uniqueness theorem: it forces $\operatorname{tr} B = \operatorname{tr} C =
--   \det B = \det C = 0$ and $\operatorname{tr}(BC) = 1/\rho$, from which the candidate matrix $H_u$ is
--   recovered up to algebraic equivalence.
--
--   Source: Carlo Perassi, the displayed identity inside his proof that the $2\times2$
--   obstruction is unique; the proof is unpublished, and the form $c\,\mathcal{Q}_\rho$ it is matched against is given by Theorem 4.2 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). The identity itself is classical; no novelty is claimed for it.

import Mathlib

open ComplexConjugate

theorem Diaz.det_add_two {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) :
    (X + Y).det = X.det + Y.det + Matrix.trace X * Matrix.trace Y - Matrix.trace (X * Y) := by sorry
