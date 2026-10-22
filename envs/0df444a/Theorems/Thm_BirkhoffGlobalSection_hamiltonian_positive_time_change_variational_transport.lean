-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_positive_time_change_variational_transport
-- name    : BirkhoffGlobalSection.hamiltonian_positive_time_change_variational_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:14:27.60637+00:00
-- url     : https://prove2.me/theorems/92168684-bd95-4ae3-be57-e01ab940104c
-- title:
--   Hamiltonian positive time change variational transport
-- statement:
--   A supplied Hamiltonian variational matrix and positive time change yield the stated shear-corrected variation for the scaled Hamiltonian field, while preserving its transverse coordinates.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 4 of the Proved theorem BirkhoffGlobalSection.positive_time_change_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_positive_time_change_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.hamiltonian_positive_time_change_variational_transport :
∀ (F : Phase → ℝ) (b : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) (τ : ℝ → ℝ)
    (hx : ∀ s, HasDerivAt x (hamiltonianVectorField F (x s)) s)
    (hY : ∀ s, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x s)).comp (Y s)) s)
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase) (hτ0 : τ 0 = 0)
    (hτ : ∀ t, HasDerivAt τ (b (x (τ t))) t)
    (hX : ∀ t, DifferentiableAt ℝ (hamiltonianVectorField F) (x (τ t)))
    (hb : ∀ t, DifferentiableAt ℝ b (x (τ t)))
    (hpos : ∀ t, 0 < b (x (τ t)))
    (hk : ∀ v : Phase, Continuous (fun t => fderiv ℝ b (x (τ t)) (Y (τ t) v))),
    ∀ v : Phase, ∃ z : ℝ → Phase,
      z 0 = v ∧
      (∀ t, HasDerivAt z
        (fderiv ℝ (fun y => b y • hamiltonianVectorField F y) (x (τ t)) (z t)) t) ∧
      (∀ t, transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (z t) =
        transverseFrameCoordinates (TangentialHessian.grad F (x (τ t))) (Y (τ t) v)) := by sorry
