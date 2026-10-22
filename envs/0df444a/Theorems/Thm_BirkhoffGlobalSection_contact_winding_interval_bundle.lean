-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle
-- name    : BirkhoffGlobalSection.contact_winding_interval_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T13:10:52.55864+00:00
-- url     : https://prove2.me/theorems/2afd82c5-e67a-4354-9620-a5051d1aa1e2
-- title:
--   Joint contact angles and attained closed winding intervals
-- statement:
--   Ten results construct a jointly continuous positive polar lift for a nonvanishing plane family over real time and an unwrapped initial angle. Identity initial directions normalize the angle by theta(0,s)=s and make it unique. Direction-family periods give angle shifts. The normalized winding image over a full initial turn is a closed interval with attained extrema; a strict bound for every direction is equivalent to that bound at the lower endpoint. Linearity and fixed-vector time continuity yield joint continuity of a planar action. These facts are instantiated for the supplied concrete model Reeb trajectory and identity-initialized variational matrix. The geometric integer threshold rule is reused conditionally on a width below one. No interval-width bound or Conley–Zehnder identification is asserted in this bundle.
-- source:
--   Original auxiliary formalization expanding Hryniewicz, arXiv:1105.2077v5, Section 2.1.1, pp. 5–6, footnote 2 and equations (4)–(5), https://arxiv.org/pdf/1105.2077. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Supplied variational equations remain hypotheses; neither a spatial Flow derivative nor an index/global-section theorem is concluded.

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
import Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_winding_interval_bundle :
(∀ (z : ℝ × ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ x, z x ≠ 0) (a : ℂ) (ha : Complex.exp a = z (0, 0)),
    ∃ f : ℝ × ℝ → ℂ, Continuous f ∧ f (0, 0) = a ∧
      ∀ x, Complex.exp (f x) = z x) ∧
(∀ (v : ℝ × ℝ → Plane)
    (hv : Continuous v) (hne : ∀ x, v x ≠ 0)
    (hzero : ∀ s, v (0, s) = ![Real.cos s, Real.sin s]),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
(∀ (v : ℝ × ℝ → Plane)
    (ρ σ θ ψ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ x, 0 < ρ x) (hσ : ∀ x, 0 < σ x)
    (hθ0 : ∀ s, θ (0, s) = s) (hψ0 : ∀ s, ψ (0, s) = s)
    (hvθ : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (hvψ : ∀ x, v x = ![σ x * Real.cos (ψ x), σ x * Real.sin (ψ x)]),
    θ = ψ) ∧
(∀ (v : ℝ × ℝ → Plane)
    (ρ θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (hρ : ∀ x, 0 < ρ x)
    (hθ0 : ∀ s, θ (0, s) = s)
    (hpolar : ∀ x, v x = ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)])
    (P : ℝ) (hperiod : ∀ t s, v (t, s + P) = v (t, s)),
    ∀ t s, θ (t, s + P) = θ (t, s) + P) ∧
(∀ (θ : ℝ × ℝ → ℝ) (hθ : Continuous θ) (T : ℝ),
    ∃ a b : ℝ, a ≤ b ∧
      (fun s => (θ (T, s) - s) / (2 * Real.pi)) '' Icc 0 (2 * Real.pi) = Icc a b ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b)) ∧
(∀ (d : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    (∀ s ∈ Icc 0 (2 * Real.pi), c < d s) ↔ c < a) ∧
(∀ (A : ℝ → Plane → Plane)
    (hlin : ∀ t (p r : Plane) (a b : ℝ), A t (a • p + b • r) = a • A t p + b • A t r)
    (hcont : ∀ p, Continuous (fun t => A t p)),
    Continuous (fun x : ℝ × Plane => A x.1 x.2)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase),
    ∃ ρ θ : ℝ × ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ x, 0 < ρ x) ∧ (∀ s, θ (0, s) = s) ∧
      ∀ x, convexModelContactVariationPath M q Z x.1 ![Real.cos x.2, Real.sin x.2] =
        ![ρ x * Real.cos (θ x), ρ x * Real.sin (θ x)]) ∧
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
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = a) ∧
      (∃ s ∈ Icc 0 (2 * Real.pi), (θ (T, s) - s) / (2 * Real.pi) = b) ∧
      ((∀ s ∈ Icc 0 (2 * Real.pi), 2 * Real.pi < θ (T, s) - s) ↔ 1 < a)) ∧
(∀ (d : ℝ → ℝ) (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1)
    (himage : d '' Icc 0 (2 * Real.pi) = Icc a b),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔
      ∀ s ∈ Icc 0 (2 * Real.pi), (k : ℝ) < d s) := by sorry
