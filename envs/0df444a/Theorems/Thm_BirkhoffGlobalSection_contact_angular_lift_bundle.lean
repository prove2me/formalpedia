-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
-- name    : BirkhoffGlobalSection.contact_angular_lift_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T11:00:40.647977+00:00
-- url     : https://prove2.me/theorems/b7a9c5b2-a0b1-4f6a-8c55-e58d31cff6ad
-- title:
--   Continuous polar lifts and intrinsic angle increments for contact variations
-- statement:
--   Every continuous nonvanishing plane curve on $\mathbb R$ has a positive continuous radius and a continuous real angle: $v(t)=\rho(t)(\cos\theta(t),\sin\theta(t))$. Continuous positive polar descriptions have identical angular increments $\theta(t)-\theta(0)$. A continuous nonzero complex curve also admits a logarithm with any prescribed initial logarithm. For supplied model contact variations, continuity and nonvanishing follow from the variational equations and the preceding symplecticity bundle. A strict winding lower bound for every lift is equivalent to that bound for one existing lift. These eight results do not define an index or construct a global section.
-- source:
--   Original auxiliary results for the Birkhoff global-section formalization. Hamiltonian/contact conventions: Hryniewicz arXiv:1105.2077v5, equations (1)-(2) and Section 2.1.1. Calculus, Hessian symmetry, covering lifts and finite-dimensional injectivity/surjectivity: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. These are explicit auxiliary proofs, not a claimed Conley-Zehnder index or prescribed-binding theorem.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_angular_lift_bundle :
(∀ (z : ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ t, z t ≠ 0) (a : ℂ) (ha : Complex.exp a = z 0),
    ∃ f : ℝ → ℂ, Continuous f ∧ f 0 = a ∧ ∀ t, Complex.exp (f t) = z t) ∧
(∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧
      (∀ t, 0 < ρ t) ∧ ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
(∀ (θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ t, Real.cos (θ t) = Real.cos (ψ t))
    (hsin : ∀ t, Real.sin (θ t) = Real.sin (ψ t)),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ (v : Plane) (ρ σ θ ψ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : v = ![ρ * Real.cos θ, ρ * Real.sin θ])
    (hψ : v = ![σ * Real.cos ψ, σ * Real.sin ψ]),
    ρ = σ ∧ Real.cos θ = Real.cos ψ ∧ Real.sin θ = Real.sin ψ) ∧
(∀ (v : ℝ → Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, v t = ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane) (hp : p ≠ 0),
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      ∀ t, convexModelContactVariationPath M q Z t p =
        ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (p : Plane) (ρ σ θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hρ : ∀ t, 0 < ρ t) (hσ : ∀ t, 0 < σ t)
    (hvθ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)])
    (hvψ : ∀ t, convexModelContactVariationPath M q Z t p =
      ![σ t * Real.cos (ψ t), σ t * Real.sin (ψ t)]),
    ∀ t, θ t - θ 0 = ψ t - ψ 0) ∧
(∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) (T L : ℝ),
    (∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ v t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      L < θ T - θ 0) ↔
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧ L < θ T - θ 0) := by sorry
