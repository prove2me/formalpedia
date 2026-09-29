-- Prove2me | Theorems.Thm_Diaz_Hmat_pencil_normal_form
-- name    : Diaz.Hmat_pencil_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:48.072964+00:00
-- url     : https://prove2.me/theorems/4cd1db50-32d6-4535-bb3f-42b34f68e7b1
-- title:
--   The pencil normal form of the candidate matrix: $H_u=A_0(I+B_0u+C_0\bar u)$ with $B_0^2=C_0^2=0$
-- statement:
--   **The candidate matrix in pencil normal form.**
--
--   Let $r \neq 0$ and let $H_u = \begin{pmatrix} u & r \\ r & \bar u\end{pmatrix}$ be the matrix attached to
--   a Diaz candidate. Put
--
--   $$A_0 = \begin{pmatrix}0 & r\\ r & 0\end{pmatrix}, \qquad
--   B_0 = \frac{1}{r}\begin{pmatrix}0&0\\1&0\end{pmatrix}, \qquad
--   C_0 = \frac{1}{r}\begin{pmatrix}0&1\\0&0\end{pmatrix}.$$
--
--   Then
--
--   $$A_0\bigl(I + u B_0 + \bar u\, C_0\bigr) = H_u, \qquad B_0^2 = C_0^2 = 0, \qquad
--   \operatorname{tr}(B_0 C_0) = \frac{1}{r^2}.$$
--
--   **Why.** Four entrywise computations.
--
--   **Role.** This is the factorisation displayed after Theorem 4.2 of the note cited below, and the explicit witness that closes Carlo Perassi's full uniqueness theorem for the $2\times2$ obstruction, whose determinantal part is that Theorem 4.2; the full theorem is unpublished.
--   The full theorem shows every singular $M \in M_2(W_u)$ without a vanishing algebraic matrix coefficient
--   satisfies, after normalising $A$ to the identity, exactly the three identities $B^2 = C^2 = 0$ and
--   $\operatorname{tr}(BC) = 1/\rho$; the pair $(B_0, C_0)$ displayed here satisfies them, and since all
--   non-zero square-zero $2\times2$ matrices are $\mathrm{GL}_2$-conjugate, $M = P H_u Q$ follows. In other
--   words $H_u$ is not one obstruction among many inside the candidate's hull: up to algebraic equivalence it
--   is the only one. Note that $r^2 = \rho = u\bar u$ for a candidate, so $\operatorname{tr}(B_0C_0) = 1/\rho$.
--
--   Source: Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 4 (*The precise open
--   boundary*), the factorisation displayed after Theorem 4.2 (*Uniqueness of the obstruction*). No novelty is claimed.

import Mathlib
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz

theorem Diaz.Hmat_pencil_normal_form {u r : ℂ} (hr : r ≠ 0) :
    !![0, r; r, 0] *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + u • !![0, 0; r⁻¹, 0] + (conj u) • !![0, r⁻¹; 0, 0])
        = Hmat u r
      ∧ (!![0, 0; r⁻¹, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; r⁻¹, 0] = 0
      ∧ (!![0, r⁻¹; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, r⁻¹; 0, 0] = 0
      ∧ Matrix.trace ((!![0, 0; r⁻¹, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, r⁻¹; 0, 0])
          = (r ^ 2)⁻¹ := by sorry
