-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
-- name    : BirkhoffGlobalSection.model_contact_rate_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T13:16:18.857842+00:00
-- url     : https://prove2.me/theorems/6d29377e-c237-4d30-a2c9-678ab91f8b36
-- title:
--   Smooth model contact normalization and transfer of transverse winding
-- statement:
--   Let $M$ be a convex regularization model, $H$ its model Hamiltonian, and $r(y)=\alpha_y(X_H(y))$ on its frontier. The bundle derives smoothness of $X_H$, $r$, and $b=1/r$, and positivity of $b$:
--   $$r(y)>0,\qquad b(y)=1/r(y)>0.$$
--   It supplies the continuous functional coefficients and regularity required by the positive-time-change theorem. For a supplied Hamiltonian trajectory, complete order clock and normalized variational matrix, an assumed Hamiltonian transverse winding bound above $2\pi$ transfers to the corresponding normalized time. The bound still uses the quaternionic Hamiltonian coordinates; neither radial index identification nor dynamical convexity is asserted.
--
--   **Formalization Note.** This theorem is the conjunction of 6 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/MODEL_CONTACT_RATE_WINDING.md.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.model_contact_rate_bundle :
(∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    ContDiffAt ℝ ∞ (hamiltonianVectorField F) y) ∧
(∀ (X : Phase → Phase) (y : Phase)
    (hX : ContDiffAt ℝ ∞ X y),
    ContDiffAt ℝ ∞ (fun x => phaseRadialContact x (X x)) y) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    let r : Phase → ℝ := fun x =>
      phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x)
    ContDiffAt ℝ ∞ (hamiltonianVectorField M.modelHamiltonian) y ∧
      ContDiffAt ℝ ∞ r y ∧ ContDiffAt ℝ ∞ (fun x => (r x)⁻¹) y ∧
      0 < (r y)⁻¹) ∧
(∀ (b : Phase → ℝ) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase))
    (hx : Continuous x) (hZ : Continuous Z)
    (hb : ∀ t, ContDiffAt ℝ ∞ b (x t)) (hne : ∀ t, b (x t) ≠ 0),
    Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x : ℝ → Phase)
    (C : ℝ ≃o ℝ) (Z : ℝ → (Phase →L[ℝ] Phase))
    (hx : Continuous x) (hZ : Continuous Z)
    (hs : ∀ t, x t ∈ frontier M.body),
    let b : Phase → ℝ := fun y =>
      (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹
    (∀ t, DifferentiableAt ℝ (hamiltonianVectorField M.modelHamiltonian) (x t)) ∧
    (∀ t, DifferentiableAt ℝ b (x t)) ∧ (∀ t, 0 < b (x t)) ∧
    Continuous (fun t => (b (x t))⁻¹ •
      ((fderiv ℝ b (x t)).comp (Z (C t))))) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C
      (phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t))) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x (C.symm t))).comp (Z t)) t)
    (v : Phase) (hv : fderiv ℝ M.modelHamiltonian (x 0) v = 0)
    (hvn : transverseFrameCoordinates
      (TangentialHessian.grad M.modelHamiltonian (x 0)) v ≠ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian (x (C.symm t))) (Z t v) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0) := by sorry
