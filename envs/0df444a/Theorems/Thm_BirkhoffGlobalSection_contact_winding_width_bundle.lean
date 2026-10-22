-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_winding_width_bundle
-- name    : BirkhoffGlobalSection.contact_winding_width_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T13:39:22.651623+00:00
-- url     : https://prove2.me/theorems/cc511312-4afe-4355-a090-69d813e194ad
-- title:
--   Strict half-turn width of the concrete contact winding interval
-- statement:
--   Seven results show that the closed winding interval of the supplied concrete contact variational action has width strictly below one half. Preserved area prevents a continuous ordered angular gap from crossing zero or pi. Linearity gives antipodal angle shifts and pi-periodic increments. Reducing arbitrary initial angles modulo pi yields a strict half-turn bound between every pair of winding values; attained extrema give the interval width. The concrete conclusion constructs the normalized jointly continuous polar description and closed winding image, derives the width without an added width hypothesis, and shows that ceil(a)+ceil(b)-1 is at least three exactly when every directional winding exceeds one. The integer expression is the geometric interval rule; this does not yet identify it with the Conley–Zehnder index.
-- source:
--   Original auxiliary formalization expanding Hryniewicz, arXiv:1105.2077v5, Section 2.1.1, pp. 5–6, footnote 2 and equations (4)–(5), https://arxiv.org/pdf/1105.2077. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Supplied variational equations remain hypotheses; neither a spatial Flow derivative nor an index/global-section theorem is concluded.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle
import Mathlib.Algebra.Ring.Periodic
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_winding_width_bundle :
(∀ (g : ℝ → ℝ) (hg : Continuous g)
    (h0 : 0 < g 0) (hpi : g 0 < Real.pi)
    (hne0 : ∀ t, g t ≠ 0) (hnepi : ∀ t, g t ≠ Real.pi),
    ∀ t, 0 < g t ∧ g t < Real.pi) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (s r : ℝ) (hsr : s < r) (hr : r - s < Real.pi),
    ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (hneg : ∀ t p, A t (-p) = -(A t p)),
    ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi) ∧
(∀ (θ : ℝ × ℝ → ℝ)
    (hshift : ∀ t s, θ (t, s + Real.pi) = θ (t, s) + Real.pi)
    (hgap : ∀ s r, s < r → r - s < Real.pi →
      ∀ t, 0 < θ (t, r) - θ (t, s) ∧ θ (t, r) - θ (t, s) < Real.pi)
    (T s r : ℝ),
    |((θ (T, r) - r) / (2 * Real.pi)) - ((θ (T, s) - s) / (2 * Real.pi))| < 1 / 2) ∧
(∀ (d : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b)
    (hbound : ∀ s r, |d r - d s| < 1 / 2),
    b - a < 1 / 2) ∧
(∀ (A : ℝ → Plane → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ t s, A t ![Real.cos s, Real.sin s] =
      ![ρ (t, s) * Real.cos (θ (t, s)), ρ (t, s) * Real.sin (θ (t, s))])
    (harea : ∀ t p r, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0)
    (hneg : ∀ t p, A t (-p) = -(A t p)) (T a b : ℝ) (hab : a ≤ b)
    (himage : (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b),
    b - a < 1 / 2) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (T : ℝ),
    ∃ (ρ θ : ℝ × ℝ → ℝ) (a b : ℝ), Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      (∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
      a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      b - a < 1 / 2 ∧
      ((3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔
        ∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s)) := by sorry
