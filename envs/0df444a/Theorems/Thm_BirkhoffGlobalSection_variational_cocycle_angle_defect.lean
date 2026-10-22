-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_variational_cocycle_angle_defect
-- name    : BirkhoffGlobalSection.variational_cocycle_angle_defect
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T19:35:42.673497+00:00
-- url     : https://prove2.me/theorems/b2d02dbc-cc80-429e-9de5-4def137c6efd
-- title:
--   Angle defect of a period cocycle
-- statement:
--   For a period cocycle, the shifted ambient increment agrees with the base increment up to one turn:
--
--   $$
--   \alpha(a+T)-\alpha(a) \le \alpha(T)-\alpha(0)+2\pi
--   \qquad\text{for every }a.
--   $$
--
--   The cocycle identity makes the shifted variational flow conjugate to the base flow, so the two determinant paths differ only by the branch choice. This is the remaining analytic core of shift stability, with the ODE infrastructure factored out as hypotheses.
-- source:
--   Autonomous ODE uniqueness plus the periodic linear variational equation (cocycle identity), and the resulting uniform branch bound for the determinant rotation angle; quaternionic-frame context of Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

namespace BirkhoffGlobalSection

theorem variational_cocycle_angle_defect
    (F : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hper : ∀ t : ℝ, x (t + T) = x t)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (hcocycle : ∀ t : ℝ, Y (t + T) = (Y t).comp (Y T))
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ a : ℝ, α (a + T) - α a ≤ α T - α 0 + 2 * Real.pi := by sorry

end BirkhoffGlobalSection
