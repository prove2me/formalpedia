-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_reeb_bundle
-- name    : BirkhoffGlobalSection.weighted_reeb_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T12:48:11.48792+00:00
-- url     : https://prove2.me/theorems/57c7d6d9-670b-458e-b2fd-0fb3018ad499
-- title:
--   Explicit weighted-sphere Reeb formula, uniqueness and smoothness
-- statement:
--   Let $u\in S^3\subset\mathbb R^4$, let $f(u)>0$ with $f$ differentiable at $u$, and put $\beta=f\alpha$. The explicit coordinate formula in the formal statement gives the unique sphere-tangent vector $R$ satisfying
--   $$\beta_u(R)=1,\qquad d\beta_u(R,w)=0\quad(w\in T_uS^3).$$
--   The bundle proves the formula, existence and uniqueness, smoothness of the raw formula when $f$ is smooth near $u$, and the inverse-gauge specialization for a compact convex body with the origin in its interior and a smooth radial chart. Exterior derivatives are actual derivatives of the weighted primitive. This supplies a reusable concrete Reeb-field interface.
--
--   **Formalization Note.** This theorem is the conjunction of 4 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/WEIGHTED_SPHERE_REEB.md.

import Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.weighted_reeb_bundle :
(∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let L := fderiv ℝ f u
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := ((f u) ^ 2)⁻¹ •
      ((2 * f u + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
    (f u * phaseRadialContact u R = 1) ∧
    (∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) ∧
(∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) ∧
(∀ (f : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f u) (hpos : 0 < f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase → Phase := fun x i => fderiv ℝ f x (coordinateVector i)
    let R : Phase → Phase := fun x => ((f x) ^ 2)⁻¹ •
      ((2 * f x + fderiv ℝ f x x) • J x - J (g x) -
        (fderiv ℝ f x (J x)) • x)
    ContDiffAt ℝ ∞ R u) ∧
(∀ (B : Set Phase)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u),
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) := by sorry
