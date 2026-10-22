-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_contact_normalized_transverse_winding
-- name    : BirkhoffGlobalSection.convex_model_contact_normalized_transverse_winding
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:28.632975+00:00
-- url     : https://prove2.me/theorems/2455d17b-96d1-4d89-94c2-51c7a2e92bfc
-- title:
--   Convex model contact normalized transverse winding
-- statement:
--   For the supplied convex model trajectories, clock and variational matrix, the original transverse winding bound transfers to contact-normalized time under the displayed differential hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.model_contact_rate_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_model_contact_rate_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_contact_normalized_transverse_winding :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (x : ℝ → Phase) (C : ℝ ≃o ℝ)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (T S : ℝ)
    (hs : ∀ t, x t ∈ frontier M.body)
    (hwind : HasTransverseWindingAboveOne M.modelHamiltonian x T)
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField M.modelHamiltonian (x t)) t)
    (hC0 : C 0 = 0) (hCT : C T = S)
    (hC : ∀ t, HasDerivAt C
      (phaseRadialContact (x t) (hamiltonianVectorField M.modelHamiltonian (x t))) t)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase)
    (hZ : ∀ t, HasDerivAt Z
      ((fderiv ℝ (fun y =>
        (phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y))⁻¹ •
          hamiltonianVectorField M.modelHamiltonian y) (x (C.symm t))).comp (Z t)) t)
    (v : Phase) (hv : fderiv ℝ M.modelHamiltonian (x 0) v = 0)
    (hvn : transverseFrameCoordinates
      (TangentialHessian.grad M.modelHamiltonian (x 0)) v ≠ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧
        transverseFrameCoordinates
          (TangentialHessian.grad M.modelHamiltonian (x (C.symm t))) (Z t v) =
            ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      2 * Real.pi < θ S - θ 0 := by sorry
