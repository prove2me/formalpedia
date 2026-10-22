-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_angle_exists
-- name    : BirkhoffGlobalSection.ambient_rotation_angle_exists
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:33:29.925372+00:00
-- url     : https://prove2.me/theorems/361bf09b-bf25-480d-9efe-d3f5c7040a68
-- title:
--   Existence of the ambient determinant rotation angle
-- statement:
--   Let $Y(t)$ be the identity-normalized fundamental solution of the Hamiltonian variational equation along a trajectory of a smooth Hamiltonian $F$. Then there exists a continuous ambient rotation angle $\alpha$: a continuous real lift of the argument of the determinant of the complex-linear part of $Y(t)$.
--
--   $$
--   \det(Y(t)_{\mathbb C}) = \rho(t) e^{i\alpha(t)}, \qquad \rho > 0.
--   $$
--
--   The point is that the variational flow is symplectic, so by Gutt's determinant rotation construction the complex-linear-part determinant never vanishes and admits a global continuous argument. One angle works for every transported vector.
-- source:
--   Auxiliary consequence of the quaternionic frame and reduced variational flow in Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, and the complex-linear determinant rotation map in Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem ambient_rotation_angle_exists
    (F : Phase → ℝ) (x : ℝ → Phase)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    ∃ α : ℝ → ℝ, IsAmbientRotationAngle Y α := by sorry

end BirkhoffGlobalSection
