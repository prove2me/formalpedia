-- Prove2me | Theorems.Thm_Diaz_Hmat_real_congr
-- name    : Diaz.Hmat_real_congr
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:51.485242+00:00
-- url     : https://prove2.me/theorems/ab6d0299-d310-4b5a-90b5-3dccc842f9b1
-- title:
--   Real congruence normal form: $Q^{\mathsf T}H_uQ=\begin{pmatrix}r+x&-y\\-y&r-x\end{pmatrix}$
-- statement:
--   **The candidate matrix is algebraically congruent to a real symmetric matrix.**
--
--   Write $u = x + iy$ with $x,y$ real, let $r \in \mathbb{C}$, and put
--
--   $$Q = \frac{1}{\sqrt 2}\begin{pmatrix}1 & i\\ 1 & -i\end{pmatrix}.$$
--
--   Then, with $H_u = \begin{pmatrix}u & r\\ r & \bar u\end{pmatrix}$,
--
--   $$Q^{\mathsf T} H_u Q = \begin{pmatrix} r + x & -y \\ -y & r - x\end{pmatrix}.$$
--
--   **Why.** A direct computation, using $u + \bar u = 2x$ and $i(u - \bar u)/2 = -y$.
--
--   **Role.** This is the congruence opening a real projection normal form of Carlo Perassi's. It converts the
--   rank-one obstruction attached to a candidate into a real symmetric matrix $G_u$, which after division by
--   its trace $2r$ becomes a real rank-one orthogonal projection with entries in the augmented logarithm
--   space. That reformulation is what makes a particularly narrow sufficient target visible: *prove that
--   every real rank-one orthogonal projection in $M_2(\widetilde{\mathcal L})$ has an image or kernel line
--   defined over $\overline{\mathbb{Q}}$*. Such a statement would exclude a Diaz candidate while asking much
--   less than the full augmented Matrix Coefficient Conjecture.
--
--   The Lean statement takes $r$ and the decomposition $u = x + iy$ as data, so it is the pure matrix
--   identity with no arithmetic hypothesis attached.
--
--   Source: Carlo Perassi; unpublished apart from this node. No novelty is
--   claimed.

import Mathlib
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz

theorem Diaz.Hmat_real_congr (u r : ℂ) (x y : ℝ) (hu : u = (x : ℂ) + (y : ℂ) * Complex.I) :
    Matrix.transpose (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, Complex.I; 1, -Complex.I]) *
        Hmat u r * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • !![1, Complex.I; 1, -Complex.I])
      = !![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)] := by sorry
