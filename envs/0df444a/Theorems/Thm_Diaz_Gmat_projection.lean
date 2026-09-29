-- Prove2me | Theorems.Thm_Diaz_Gmat_projection
-- name    : Diaz.Gmat_projection
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:38.098587+00:00
-- url     : https://prove2.me/theorems/330f56c7-5a55-40f0-968d-b6e9da483412
-- title:
--   $G_u/(2r)$ is a rank-one projection: $\det G_u=0$, $\operatorname{tr}G_u=2r$, $P_u^2=P_u$
-- statement:
--   **The real form of the candidate matrix is $2r$ times a rank-one projection.**
--
--   Write $u = x + iy$ with $x, y$ real, let $r \neq 0$, and assume the candidate relation
--   $u \bar u = r^2$. Put
--
--   $$G_u = \begin{pmatrix} r + x & -y \\ -y & r - x\end{pmatrix}.$$
--
--   Then $\det G_u = 0$, $\operatorname{tr} G_u = 2r$, and $P_u := G_u/(2r)$ is idempotent:
--   $P_u^2 = P_u$.
--
--   **Why.** The hypothesis $u\bar u = r^2$ says exactly $x^2 + y^2 = r^2$, whence
--   $\det G_u = r^2 - x^2 - y^2 = 0$; the trace is immediate; and a $2\times2$ matrix with zero determinant
--   satisfies $G^2 = (\operatorname{tr}G)\,G$, so $P_u^2 = P_u$.
--
--   **Role.** This is the substance of a real projection normal form of Carlo Perassi's: the obstruction
--   attached to a Diaz candidate can be presented as a genuine real rank-one orthogonal projection whose
--   entries lie in the augmented logarithm space $\widetilde{\mathcal L}$ — because $x = (u+\bar u)/2$ and
--   $iy = (u - \bar u)/2$ are logarithms and $r$ is algebraic. He then observes that the
--   projection has no vanishing non-zero algebraic matrix coefficient and that its spectral slopes lie
--   outside $\widetilde{\mathcal L}$, which is what turns "every real rank-one orthogonal projection over
--   $\widetilde{\mathcal L}$ has an algebraic image or kernel line" into a sufficient target for Diaz's
--   conjecture. The Lean statement isolates the projection property itself, which is unconditional.
--
--   Source: Carlo Perassi; unpublished apart from this node. Elementary; no novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.Gmat_projection {u r : ℂ} (x y : ℝ) (hu : u = (x : ℂ) + (y : ℂ) * Complex.I)
    (hr : r ≠ 0) (h : u * conj u = r ^ 2) :
    (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]).det = 0
      ∧ Matrix.trace (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]) = 2 * r
      ∧ ((2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]))
          * ((2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]))
        = (2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]) := by sorry
