-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
-- name    : BirkhoffGlobalSection.contact_variation_preservation_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T21:12:21.991198+00:00
-- url     : https://prove2.me/theorems/9a8cecca-c085-4fcb-9aa0-04813aaf87ae
-- title:
--   Contact preservation and continuous linearized coefficient action
-- statement:
--   For a smooth positive sphere weight $f$, put $\beta=f\alpha$ and let $R$ be its concrete Reeb extension. Along supplied solutions $q'=R(q)$ and $v'=DR(q)v$, with $q$ sphere-valued and $v(0)$ tangent, the weighted contact evaluation is conserved:
--   $$\beta_{q(t)}(v(t))=\beta_{q(0)}(v(0)).$$
--   Thus initially contact vectors remain contact. The bundle gives the radial and weighted contact differentiation rules and the tangent derivative of Reeb normalization used by this result.
--
--   For a convex model and supplied variational matrix $Z'=DR(q)\circ Z$ with $Z(0)=\mathrm{id}$, define
--   $$A(t)p=C_{q(t)}\big(Z(t)(p_0s_0(q(0))+p_1s_1(q(0)))\big).$$
--   The action is linear, is the identity at zero, is continuous in time for each fixed $p$, and exactly reconstructs the transported contact vector in the current frame. This does not prove symplecticity, invertibility, fundamental matrix existence or equality with a spatial derivative of the complete Flow.
--
--   **Formalization Note.** This theorem is the conjunction of 11 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/CONTACT_VARIATION_PRESERVATION.md.

import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_variation_preservation_bundle :
(∀ (q v : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => phaseRadialContact (q s) (v s))
      (phaseRadialContact a (v t) + phaseRadialContact (q t) b) t) ∧
(∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : DifferentiableAt ℝ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => f (q s) * phaseRadialContact (q s) (v s))
      (fderiv ℝ f (q t) a * phaseRadialContact (q t) (v t) +
        f (q t) * (phaseRadialContact a (v t) + phaseRadialContact (q t) b)) t) ∧
(∀ (f : Phase → ℝ) (u w : Phase)
    (hu : u ∈ unitThreeSphere)
    (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0)
    (hf : ∀ x ∈ unitThreeSphere, ContDiffAt ℝ ∞ f x ∧ 0 < f x),
    let R := sphereReebExtension f
    fderiv ℝ f u w * phaseRadialContact u (R u) +
      f u * (phaseRadialContact w (R u) +
        phaseRadialContact u (fderiv ℝ R u w)) = 0) ∧
(∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0),
    ∀ t, f (q t) * phaseRadialContact (q t) (v t) =
      f (q 0) * phaseRadialContact (q 0) (v 0)) ∧
(∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (hf : ∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ f u ∧ 0 < f u)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (sphereReebExtension f (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (sphereReebExtension f) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hα0 : phaseRadialContact (q 0) (v 0) = 0),
    ∀ t, phaseRadialContact (q t) (v t) = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hα0 : phaseRadialContact (q 0) (v 0) = 0),
    ∀ t, (q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0) ∧
      phaseRadialContact (q t) (v t) = 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hq : Continuous q) (hv : Continuous v) (hs : ∀ t, q t ∈ unitThreeSphere),
    Continuous (fun t => convexModelContactCoordinates M (q t) (v t))) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) (p r : Plane) (a b : ℝ),
    convexModelContactVariationPath M q Z t (a • p + b • r) =
      a • convexModelContactVariationPath M q Z t p +
        b • convexModelContactVariationPath M q Z t r) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : q 0 ∈ unitThreeSphere)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    convexModelContactVariationPath M q Z 0 p = p) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : Continuous q) (hZ : Continuous Z) (p : Plane),
    Continuous (fun t => convexModelContactVariationPath M q Z t p)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    let e := p 0 • convexModelSymplecticContactFrame M (q 0) 0 +
      p 1 • convexModelSymplecticContactFrame M (q 0) 1
    ∀ t, (q t 0 * Z t e 0 + q t 1 * Z t e 1 +
        q t 2 * Z t e 2 + q t 3 * Z t e 3 = 0) ∧
      phaseRadialContact (q t) (Z t e) = 0 ∧
      Z t e = convexModelContactVariationPath M q Z t p 0 •
          convexModelSymplecticContactFrame M (q t) 0 +
        convexModelContactVariationPath M q Z t p 1 •
          convexModelSymplecticContactFrame M (q t) 1) := by sorry
