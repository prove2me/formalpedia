-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
-- name    : BirkhoffGlobalSection.variational_symplecticity_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T10:35:28.279785+00:00
-- url     : https://prove2.me/theorems/d026730f-75b7-49af-8c48-a8fa8016acab
-- title:
--   Exterior pairing conservation and invertible contact variational action
-- statement:
--   For a smooth Hamiltonian $F$, its linearization preserves $\omega$ infinitesimally. Any differentiable scalar multiple $bX_F$ has the same property on energy-tangent vectors, and two supplied energy-tangent variations have constant symplectic pairing. For a convex regularization model, initially sphere-tangent solutions of the concrete Reeb variational equation conserve the actual exterior derivative of $f\alpha$, where $f=\operatorname{gauge}^{-2}$. The normalized pairing-one contact frame identifies this exterior pairing with standard area. Consequently the supplied contact coefficient action $A(t)$ preserves $p_0r_1-p_1r_0$, is bijective, and sends nonzero vectors to nonzero vectors. The bundle contains 13 individually quantified results. Fundamental-matrix existence and spatial differentiability of the complete Flow are not concluded.
-- source:
--   Original auxiliary results for the Birkhoff global-section formalization. Hamiltonian/contact conventions: Hryniewicz arXiv:1105.2077v5, equations (1)-(2) and Section 2.1.1. Calculus, Hessian symmetry, covering lifts and finite-dimensional injectivity/surjectivity: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. These are explicit auxiliary proofs, not a claimed Conley-Zehnder index or prescribed-binding theorem.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.variational_symplecticity_bundle :
(∀ (v w : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t),
    HasDerivAt (fun s => phaseSymplecticForm (v s) (w s))
      (phaseSymplecticForm a (w t) + phaseSymplecticForm (v t) b) t) ∧
(∀ (F : Phase → ℝ) (y v : Phase),
    phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v) ∧
(∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w =
      fderiv ℝ (fderiv ℝ F) y v w) ∧
(∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
      phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0) ∧
(∀ (F b : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) (hb : DifferentiableAt ℝ b y)
    (hv : fderiv ℝ F y v = 0) (hw : fderiv ℝ F y w = 0),
    phaseSymplecticForm (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y v) w +
      phaseSymplecticForm v (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y w) = 0) ∧
(∀ (F b : Phase → ℝ) (q v w : ℝ → Phase)
    (hF : ∀ t, ContDiffAt ℝ ∞ F (q t))
    (hb : ∀ t, DifferentiableAt ℝ b (q t))
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (w t)) t)
    (hvE : ∀ t, fderiv ℝ F (q t) (v t) = 0)
    (hwE : ∀ t, fderiv ℝ F (q t) (w t) = 0),
    ∀ t, phaseSymplecticForm (v t) (w t) = phaseSymplecticForm (v 0) (w 0)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v w : ℝ → Phase)
    (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (convexModelSphereReebField M) (q t) (w t)) t)
    (hv0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hw0 : q 0 0 * w 0 0 + q 0 1 * w 0 1 + q 0 2 * w 0 2 + q 0 3 * w 0 3 = 0),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    ∀ t, (fderiv ℝ (fun x => f x * phaseRadialContact x (w t)) (q t) (v t) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v t)) (q t) (w t)) =
      (fderiv ℝ (fun x => f x * phaseRadialContact x (w 0)) (q 0) (v 0) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (v 0)) (q 0) (w 0))) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (p r : Plane),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    (-phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B))) = p 0 * r 1 - p 1 * r 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p r : Plane),
    convexModelContactVariationPath M q Z t p 0 * convexModelContactVariationPath M q Z t r 1 -
      convexModelContactVariationPath M q Z t p 1 * convexModelContactVariationPath M q Z t r 0 =
      p 0 * r 1 - p 1 * r 0) ∧
(∀ (A : Plane → Plane)
    (hA : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Injective A) ∧
(∀ (A : Plane → Plane)
    (hlin : ∀ (p r : Plane) (a b : ℝ), A (a • p + b • r) = a • A p + b • A r)
    (harea : ∀ p r, A p 0 * A r 1 - A p 1 * A r 0 = p 0 * r 1 - p 1 * r 0),
    Function.Bijective A) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ),
    Function.Bijective (convexModelContactVariationPath M q Z t)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (t : ℝ) (p : Plane) (hp : p ≠ 0),
    convexModelContactVariationPath M q Z t p ≠ 0) := by sorry
