-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_transverse_bound
-- name    : BirkhoffGlobalSection.ambient_rotation_transverse_bound
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T17:33:32.306189+00:00
-- url     : https://prove2.me/theorems/e41629ee-69a8-41ab-97e2-69c98db792ec
-- title:
--   Ambient rotation controls transverse winding up to 4pi
-- statement:
--   Let $x$ be a closed Hamiltonian solution of period $T$ for a smooth $F$ with nonzero differential along the orbit, with variational flow $Y$, and let $\alpha$ be a continuous ambient determinant angle for $Y$. Then for every transverse tangent vector $v$ and every continuous polar angle $\theta$ of its transported quaternionic frame coordinates, the ambient increment over any period interval is controlled by the transverse increment up to $4\pi$:
--
--   $$
--   \alpha(a+T)-\alpha(a) \le \theta(T)-\theta(0)+4\pi
--   \qquad\text{for every }a.
--   $$
--
--   Reducing the ambient rotation to the transverse frame costs at most one full turn, and moving the start of the period interval costs another; both errors are uniform in the vector, the angle, and the starting time. No nondegeneracy or least-period assumption is needed.
-- source:
--   Auxiliary consequence of the quaternionic frame and reduced variational flow in Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, and the complex-linear determinant rotation map in Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem ambient_rotation_transverse_bound
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
        ∀ a : ℝ, α (a + T) - α a ≤ θ T - θ 0 + 4 * Real.pi := by sorry

end BirkhoffGlobalSection
