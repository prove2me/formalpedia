-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_periodic_ambient_rotation_transverse_comparison
-- name    : BirkhoffGlobalSection.periodic_ambient_rotation_transverse_comparison
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:05:27.941132+00:00
-- url     : https://prove2.me/theorems/1a5ed7d6-51ca-4273-9fc7-e71699cdc326
-- title:
--   Ambient determinant rotation controls periodic transverse winding
-- statement:
--   Let $x$ be a closed Hamiltonian solution of period $T>0$ for a function $F$ that is smooth near the trajectory and has nonzero differential there. Let $Y(0)=I$ be its variational flow. There exists a continuous ambient determinant angle $\alpha$ such that, for every nonzero transverse tangent vector and every continuous polar angle $\theta$ of its transported quaternionic frame coordinates,
--
--   $$
--   \alpha(a+T)-\alpha(a)\le\theta(T)-\theta(0)+4\pi\qquad\text{for every }a\in\mathbb R.
--   $$
--
--   Tangency means that the initial vector is annihilated by $dF$; transversality means its initial coordinates against $J\nabla F$ and $K\nabla F$ are not both zero. One ambient angle works for every such vector, angle, and starting time. No nondegeneracy or least-period assumption is required.
--
--   This connects ambient variational estimates to the precise winding condition used on a regular Hamiltonian level.
--
--   **Formalization Note** This auxiliary comparison combines the cited quaternionic frame and determinant rotation constructions. It includes global angle-lift existence, frame reduction, and the change of initial time. The $4\pi$ allowance is a non-sharp uniform error, not a quoted index identity.
-- source:
--   Auxiliary consequence of the quaternionic frame and reduced variational flow in Joung–van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, and the complex-linear determinant rotation map in Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3). The stated non-sharp 4π comparison is a derived frame and periodic-cocycle estimate; it is not a numbered theorem quoted verbatim from either source.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

/-- Ambient determinant rotation controls each transverse vector's winding
on a regular closed Hamiltonian orbit, uniformly in the start of the ambient
period interval. Existence of the ambient angle lift is part of the theorem;
the bound includes both frame reduction and the change of initial time. -/
theorem periodic_ambient_rotation_transverse_comparison
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    ∃ α : ℝ → ℝ, IsAmbientRotationAngle Y α ∧
      ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
        transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
        ∀ θ : ℝ → ℝ, Continuous θ →
          (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
            transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
              ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
          ∀ a : ℝ, α (a + T) - α a ≤ θ T - θ 0 + 4 * Real.pi := by sorry

end BirkhoffGlobalSection
