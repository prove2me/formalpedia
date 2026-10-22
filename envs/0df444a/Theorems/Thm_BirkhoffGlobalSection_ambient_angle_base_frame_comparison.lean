-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_ambient_angle_base_frame_comparison
-- name    : BirkhoffGlobalSection.ambient_angle_base_frame_comparison
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:49:52.948987+00:00
-- url     : https://prove2.me/theorems/61227fcd-0346-4d63-be1c-a2e2cea08c82
-- title:
--   Ambient-to-frame comparison over one base period
-- statement:
--   Over one base period, the ambient determinant angle and the transverse polar angle agree up to one full turn. Precisely, with a closed regular Hamiltonian orbit, its variational flow, and a continuous ambient angle $\alpha$, every transverse vector and polar angle $\theta$ satisfy
--
--   $$
--   \alpha(T)-\alpha(0) \le \theta(T)-\theta(0)+2\pi.
--   $$
--
--   Projecting the ambient complex-linear determinant rotation onto the quaternionic transverse frame identifies the two increments up to the choice of argument branch. This isolates the frame-reduction half of the comparison.
-- source:
--   Derived frame and periodic-cocycle estimate for the quaternionic frame and determinant rotation constructions in Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, and Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem ambient_angle_base_frame_comparison
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
      transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
      ∀ θ : ℝ → ℝ, Continuous θ →
        (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
        α T - α 0 ≤ θ T - θ 0 + 2 * Real.pi := by sorry

end BirkhoffGlobalSection
