-- Prove2me | Theorems.Thm_Diaz_det_Hmat
-- name    : Diaz.det_Hmat
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:46.234847+00:00
-- url     : https://prove2.me/theorems/6e608b82-a352-4db2-8530-7d928852407a
-- title:
--   $\det H(u,r) = 0$: over $\mathbb{C}$ the rows of the candidate matrix are dependent
-- statement:
--   Let $u, r \in \mathbb{C}$ satisfy $u\bar u = r^{2}$, and let
--
--   $$H(u,r) = \begin{pmatrix} u & r \\ r & \bar u \end{pmatrix}.$$
--
--   Then
--
--   $$\det H(u,r) = u\bar u - r^{2} = 0.$$
--
--   **Why.** Immediate from the $2 \times 2$ determinant formula and the hypothesis.
--
--   **Role.** Half of the tension that makes $H$ interesting. The hypothesis $u\bar u = r^{2}$ says that $u$ lies on the circle of radius $r$ about the origin, with $r$ in the base field — for a hypothetical counterexample $u$ to Diaz's modulus conjecture, $r = |u|$ is algebraic and this is exactly its defining property. The determinant vanishes, so the rows of $H$ are linearly dependent **over $\mathbb{C}$**. The companion theorem `Diaz.no_vanishing_coeff` shows that no coefficient $w^{\mathsf{T}} H v$ vanishes for non-zero $w,v$ over the base field: dependent over $\mathbb{C}$, independent over $K$. That gap is a miniature of the four exponentials problem and is why $H$ sits exactly at the boundary of the Matrix Coefficient Conjecture.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Rigidity.lean#L33-L35

import Mathlib
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz
variable {K : Subfield ℂ} {u r : ℂ}

theorem Diaz.det_Hmat (h : u * conj u = r ^ 2) : (Hmat u r).det = 0 := by sorry
