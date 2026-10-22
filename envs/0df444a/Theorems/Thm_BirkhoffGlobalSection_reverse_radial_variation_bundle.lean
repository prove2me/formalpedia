-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
-- name    : BirkhoffGlobalSection.reverse_radial_variation_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T14:55:27.121802+00:00
-- url     : https://prove2.me/theorems/1a8d4917-dded-4610-9167-55fb7c316990
-- title:
--   Reverse radial variational transport and energy-tangent preservation
-- statement:
--   Let $M$ be a convex regularization model, $G$ its inverse-gauge chart, $N(y)=y/|y|$, and $X=X_H/\alpha(X_H)$. Supplied normalized trajectories and variational vectors satisfy $x'=X(x)$, $v'=DX(x)v$. Initial energy tangency is preserved:
--   $$DH_{x(0)}v(0)=0\quad\Longrightarrow\quad DH_{x(t)}v(t)=0.$$
--   The bundle realizes energy tangent vectors by frontier curves and proves that $DG$ and $DN$ are inverse on the respective tangent spaces. It derives the inverse field and variational pushforward identities. Consequently $q=N\circ x$ and $w=DN_xv$ solve the concrete sphere Reeb and variational equations, are sphere tangent, and satisfy $DG_qw=v$. Only initial energy tangency is assumed for this final correspondence; fundamental matrix existence is not asserted.
--
--   **Formalization Note.** This theorem is the conjunction of 12 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/REVERSE_RADIAL_VARIATION.md.

import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_smooth_sphere_reeb_bundle
import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.reverse_radial_variation_bundle :
(∀ (F b : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (b y • hamiltonianVectorField F y) = 0) ∧
(∀ (F : Phase → ℝ) (X : Phase → Phase)
    (x v : ℝ → Phase) (hF : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ X (x t) (v t)) t)
    (hzero : ∀ t, (fun y => fderiv ℝ F y (X y)) =ᶠ[𝓝 (x t)] (fun _ => (0 : ℝ))),
    ∀ t, fderiv ℝ F (x t) (v t) = fderiv ℝ F (x 0) (v 0)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    ∀ t, fderiv ℝ M.modelHamiltonian (x t) (v t) = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ≠ 0),
    (gauge M.body u)⁻¹ • u ∈ frontier M.body) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    ∃ γ : ℝ → Phase, γ 0 = y ∧ HasDerivAt γ w 0 ∧
      ∀ᶠ s in 𝓝 0, γ s ∈ frontier M.body) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u w : Phase) (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    fderiv ℝ radialNormalize (G u) (fderiv ℝ G u w) = w) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    fderiv ℝ radialNormalize y
      ((phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian y) =
      convexModelSphereReebField M (radialNormalize y)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (radialNormalize y)
      (fderiv ℝ radialNormalize y w) = w) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let X : Phase → Phase := fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z
    fderiv ℝ (fderiv ℝ radialNormalize) y (X y) w +
      fderiv ℝ radialNormalize y (fderiv ℝ X y w) =
      fderiv ℝ (convexModelSphereReebField M) (radialNormalize y)
        (fderiv ℝ radialNormalize y w)) ∧
(∀ (q : ℝ → Phase) (v : Phase) (t : ℝ)
    (hq : ∀ᶠ s in 𝓝 t, q s ∈ unitThreeSphere) (hd : HasDerivAt q v t),
    q t 0 * v 0 + q t 1 * v 1 + q t 2 * v 2 + q t 3 * v 3 = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y w : Phase) (hy : y ∈ frontier M.body)
    (hw : fderiv ℝ M.modelHamiltonian y w = 0),
    let u := radialNormalize y
    let v := fderiv ℝ radialNormalize y w
    u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x v : ℝ → Phase)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hx : ∀ t, HasDerivAt x
      ((phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t)))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x t) (v t)) t)
    (h0 : fderiv ℝ M.modelHamiltonian (x 0) (v 0) = 0),
    let q : ℝ → Phase := fun t => radialNormalize (x t)
    let w : ℝ → Phase := fun t => fderiv ℝ radialNormalize (x t) (v t)
    (∀ t, q t ∈ unitThreeSphere) ∧
    (∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t) ∧
    (∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t) ∧
    (∀ t, q t 0 * w t 0 + q t 1 * w t 1 + q t 2 * w t 2 + q t 3 * w t 3 = 0) ∧
    (∀ t, fderiv ℝ (fun u : Phase => (gauge M.body u)⁻¹ • u) (q t) (w t) = v t)) := by sorry
