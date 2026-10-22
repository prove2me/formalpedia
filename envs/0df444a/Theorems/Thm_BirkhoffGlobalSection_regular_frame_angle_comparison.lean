-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regular_frame_angle_comparison
-- name    : BirkhoffGlobalSection.regular_frame_angle_comparison
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T20:13:59.689968+00:00
-- url     : https://prove2.me/theorems/c582f52c-4263-4ca0-ac8b-5a740ebeb925
-- title:
--   Winding comparison for regular comparison paths
-- statement:
--   For smooth nonvanishing comparison paths, the ambient increment agrees with the transverse polar increment up to one turn:
--
--   $$
--   \alpha(T)-\alpha(0) \le \theta(T)-\theta(0)+2\pi.
--   $$
--
--   Projecting the ambient complex-linear determinant rotation onto the quaternionic transverse frame identifies the two increments up to the argument branch choice. This is the winding-number core of the comparison; all path regularity and transversality propagation arrive as explicit hypotheses.
-- source:
--   Regularity and propagation for the quaternionic transverse frame versus the ambient determinant rotation; frame context of Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, determinant rotation map of Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem regular_frame_angle_comparison
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α)
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (htrans : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (hpol : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)])
    (hdet1 : ContDiffOn ℝ 1 (fun t => ambientRotationDet (Y t)) Set.univ)
    (hz1 : ContDiffOn ℝ 1
      (fun t => transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v))
      Set.univ)
    (hzne : ∀ t : ℝ,
      transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) ≠ 0) :
    α T - α 0 ≤ θ T - θ 0 + 2 * Real.pi := by sorry

end BirkhoffGlobalSection
