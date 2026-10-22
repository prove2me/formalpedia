-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_variation_symplectic_polar_data
-- name    : BirkhoffGlobalSection.convex_model_contact_variation_symplectic_polar_data
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T22:45:08.351733+00:00
-- url     : https://prove2.me/theorems/b665670c-3810-4dca-a9db-2dc0fcc035cc
-- title:
--   Symplectic polar data of the model contact variational equation
-- statement:
--   Let $q$ be a sphere-valued trajectory of the concrete model Reeb field, and let a supplied ambient matrix solution satisfy $Z'=DR(q)\circ Z$ and $Z(0)=\mathrm{id}$. In the normalized global contact frame, the induced coefficient action $A(t)$ preserves standard area, is bijective, starts at identity, and has continuous trajectories. Every nonzero initial coefficient has a continuous positive polar lift. Every other continuous positive polar description has the same angular increment. This theorem links the published contact-preservation interface to exterior-pairing conservation and angular-lift existence/uniqueness. It assumes the matrix solution and establishes no fundamental-matrix existence, Conley--Zehnder index or global section.
-- source:
--   Original auxiliary results for the Birkhoff global-section formalization. Hamiltonian/contact conventions: Hryniewicz arXiv:1105.2077v5, equations (1)-(2) and Section 2.1.1. Calculus, Hessian symmetry, covering lifts and finite-dimensional injectivity/surjectivity: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. These are explicit auxiliary proofs, not a claimed Conley-Zehnder index or prescribed-binding theorem.

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.convex_model_contact_variation_symplectic_polar_data {μ c : ℝ} (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hZ : ∀ t, HasDerivAt Z ((fderiv ℝ (convexModelSphereReebField M) (q t)).comp (Z t)) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) :
    let A := convexModelContactVariationPath M q Z
    (∀ p r : Plane, ∀ t, A t p 0 * A t r 1 - A t p 1 * A t r 0 = p 0 * r 1 - p 1 * r 0) ∧
    (∀ t, Function.Bijective (A t)) ∧ (∀ p, A 0 p = p) ∧
    (∀ p, Continuous (fun t => A t p)) ∧
    ∀ p : Plane, p ≠ 0 → ∃ ρ θ : ℝ → ℝ,
      Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, A t p = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧
      ∀ ψ : ℝ → ℝ, Continuous ψ →
        (∀ t, ∃ σ : ℝ, 0 < σ ∧ A t p = ![σ * Real.cos (ψ t), σ * Real.sin (ψ t)]) →
        ∀ t, θ t - θ 0 = ψ t - ψ 0 := by sorry
