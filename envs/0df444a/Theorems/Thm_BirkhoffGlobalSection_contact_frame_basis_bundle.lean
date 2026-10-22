-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
-- name    : BirkhoffGlobalSection.contact_frame_basis_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T19:24:00.923301+00:00
-- url     : https://prove2.me/theorems/3f9168d6-cd7f-436f-bcf6-24fef837cc73
-- title:
--   Smooth global contact basis normalized to exterior pairing one
-- statement:
--   For the transported sphere contact pair $e_0,e_1$ of a convex regularization model, let $n>0$ be its squared gradient radius and set $s_i=e_i/\sqrt n$. The pair is smooth on the sphere, tangent and contact, and
--   $$d(f\alpha)_u(s_0,s_1)=1.$$
--   Every contact tangent vector has a unique expansion in this pair. Its coefficients are the Hamiltonian transverse coordinates of its gauge pushforward divided by $\sqrt n$. The bundle includes the quaternionic reconstruction identity, reconstruction on energy/contact and sphere contact planes, linearity and smoothness of characteristic projection, smoothness of the transported frames and radius, exterior-pair rescaling, spanning and coefficient independence. It states these basis properties explicitly, without introducing a bundled Lean Basis.
--
--   **Formalization Note.** This theorem is the conjunction of 16 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/CONTACT_FRAME_BASIS.md.

import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_frame_basis_bundle :
(∀ (F : Phase → ℝ) (y v : Phase),
    fderiv ℝ F y v = v ⬝ᵥ TangentialHessian.grad F y) ∧
(∀ (g v : Phase),
    (zNormSq g + wNormSq g) • v = (v ⬝ᵥ g) • g +
      (v ⬝ᵥ TangentialHessian.frame g 0) • TangentialHessian.frame g 0 +
      (v ⬝ᵥ TangentialHessian.frame g 1) • TangentialHessian.frame g 1 +
      (v ⬝ᵥ TangentialHessian.frame g 2) • TangentialHessian.frame g 2) ∧
(∀ (F : Phase → ℝ) (y v w : Phase) (a b : ℝ),
    characteristicContactProjection F y (a • v + b • w) =
      a • characteristicContactProjection F y v + b • characteristicContactProjection F y w) ∧
(∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0) (hα : phaseRadialContact y v = 0),
    let g := TangentialHessian.grad F y
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g v
    v = (c 0 / n) • hamiltonianContactFrame F y 0 +
      (c 1 / n) • hamiltonianContactFrame F y 1) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ M.modelHamiltonian (G u) (fderiv ℝ G u v) = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let g := TangentialHessian.grad M.modelHamiltonian (G u)
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g (fderiv ℝ G u v)
    v = (c 0 / n) • convexModelSphereContactFrame M u 0 +
      (c 1 / n) • convexModelSphereContactFrame M u 1) ∧
(∀ (F : Phase → ℝ) (V : Phase → Phase)
    (y : Phase) (hF : ContDiffAt ℝ ∞ F y) (hV : ContDiffAt ℝ ∞ V y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    ContDiffAt ℝ ∞ (fun z => characteristicContactProjection F z (V z)) y) ∧
(∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => hamiltonianContactFrame F z i) y) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSphereContactFrame M z i) u) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    ContDiffAt ℝ ∞ (convexModelFrameRadius M) u ∧ 0 < convexModelFrameRadius M u) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSymplecticContactFrame M z i) u) ∧
(∀ (f : Phase → ℝ) (u v w : Phase) (a b : ℝ)
    (hf : DifferentiableAt ℝ f u),
    fderiv ℝ (fun x => f x * phaseRadialContact x (b • w)) u (a • v) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (a • v)) u (b • w) =
      a * b * (fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B = 1) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    let v := convexModelSymplecticContactFrame M u i
    (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      phaseRadialContact u v = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let c := transverseFrameCoordinates (TangentialHessian.grad M.modelHamiltonian (G u)) (fderiv ℝ G u v)
    v = (c 0 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 0 +
      (c 1 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 1) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1 = 0),
    a = 0 ∧ b = 0) := by sorry
