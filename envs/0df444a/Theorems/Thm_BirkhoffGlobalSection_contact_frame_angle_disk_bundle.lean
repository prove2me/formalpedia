-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
-- name    : BirkhoffGlobalSection.contact_frame_angle_disk_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T20:24:32.068993+00:00
-- url     : https://prove2.me/theorems/da380ae0-bfba-4776-92ea-b41bd987086b
-- title:
--   Normalized contact coordinates, unchanged polar angles and capping-frame extension
-- statement:
--   For the normalized contact basis $s_0,s_1$ of a convex model define the coefficient map $C_u(v)$ using gauge-pushed Hamiltonian coordinates divided by the positive square root of the gradient radius. It is linear and
--   $$C_u(a s_0+b s_1)=(a,b),\qquad v=C_u(v)_0s_0+C_u(v)_1s_1$$
--   for every sphere contact tangent vector. It detects exactly the zero vector on that plane. Common positive scaling preserves a supplied polar angle and its endpoint increment, hence transfers supplied angular bounds to these normalized coefficients.
--
--   For every supplied continuous sphere-valued capping disk with prescribed boundary map, the constructed global symplectic basis pulls back continuously across the disk and agrees exactly with the chosen boundary frame. Equal parametrized boundary maps give equal chosen boundary frames. No capping disk existence, embedding, index invariance, or global-section page is inferred.
--
--   **Formalization Note.** This theorem is the conjunction of 11 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/CONTACT_FRAME_ANGLE_DISK.md.

import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle :
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v w : Phase) (a b : ℝ),
    convexModelContactCoordinates M u (a • v + b • w) =
      a • convexModelContactCoordinates M u v + b • convexModelContactCoordinates M u w) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 0) = ![1, 0] ∧
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 1) = ![0, 1]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    v = (convexModelContactCoordinates M u v 0) • convexModelSymplecticContactFrame M u 0 +
      (convexModelContactCoordinates M u v 1) • convexModelSymplecticContactFrame M u 1) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (a b : ℝ),
    convexModelContactCoordinates M u (a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1) = ![a, b]) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    convexModelContactCoordinates M u v = 0 ↔ v = 0) ∧
(∀ (p q : Plane) (a θ : ℝ)
    (ha : 0 < a) (hq : q = a • p),
    (∃ r : ℝ, 0 < r ∧ p = ![r * Real.cos θ, r * Real.sin θ]) ↔
    (∃ r : ℝ, 0 < r ∧ q = ![r * Real.cos θ, r * Real.sin θ])) ∧
(∀ (p q : ℝ → Plane) (a : ℝ → ℝ) (T B : ℝ)
    (ha : ∀ t, 0 < a t) (heq : ∀ t, q t = a t • p t)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase) (T B : ℝ)
    (hq : ∀ t, q t ∈ unitThreeSphere)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian ((gauge M.body (q t))⁻¹ • q t))
          (fderiv ℝ (fun x : Phase => (gauge M.body x)⁻¹ • x) (q t) (v t)) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ convexModelContactCoordinates M (q t) (v t) =
        ![r * Real.cos (θ t), r * Real.sin (θ t)]) → B < θ T - θ 0) ∧
(∀ {A : Type*} [TopologicalSpace A]
    {μ c : ℝ} (M : ConvexRegularizationModel μ c) (d : A → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere) (i : Fin 2),
    Continuous (fun z => convexModelSymplecticContactFrame M (d z) i)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d : ClosedDiskPoint → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere)
    (γ : {z : ClosedDiskPoint // z ∈ closedDiskBoundary} → Phase)
    (hbd : ∀ z, d z.val = γ z),
    ∃ E : ClosedDiskPoint → Fin 2 → Phase,
      (∀ i, Continuous (fun z => E z i)) ∧
      (∀ z i, (d z 0 * E z i 0 + d z 1 * E z i 1 +
        d z 2 * E z i 2 + d z 3 * E z i 3 = 0) ∧ phaseRadialContact (d z) (E z i) = 0) ∧
      (∀ z, let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
        fderiv ℝ (fun x => f x * phaseRadialContact x (E z 1)) (d z) (E z 0) -
          fderiv ℝ (fun x => f x * phaseRadialContact x (E z 0)) (d z) (E z 1) = 1) ∧
      (∀ z v, d z 0 * v 0 + d z 1 * v 1 + d z 2 * v 2 + d z 3 * v 3 = 0 →
        phaseRadialContact (d z) v = 0 →
        v = convexModelContactCoordinates M (d z) v 0 • E z 0 +
          convexModelContactCoordinates M (d z) v 1 • E z 1) ∧
      (∀ z (a b : ℝ), a • E z 0 + b • E z 1 = 0 → a = 0 ∧ b = 0) ∧
      (∀ z i, E z.val i = convexModelSymplecticContactFrame M (γ z) i)) ∧
(∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d₁ d₂ : ClosedDiskPoint → Phase)
    (hbd : ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, d₁ z.val = d₂ z.val),
    ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, ∀ i : Fin 2,
      convexModelSymplecticContactFrame M (d₁ z.val) i =
        convexModelSymplecticContactFrame M (d₂ z.val) i) := by sorry
