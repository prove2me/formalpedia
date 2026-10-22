-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_variation_exterior_pairing_conserved
-- name    : BirkhoffGlobalSection.convex_model_variation_exterior_pairing_conserved
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:49:05.356235+00:00
-- url     : https://prove2.me/theorems/88655a4d-4ff4-4932-9556-783573be1281
-- title:
--   Convex model variation exterior pairing conserved
-- statement:
--   For supplied tangent contact variations along a convex model sphere Reeb trajectory, their weighted exterior pairing is conserved.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_variation_exterior_pairing_conserved :
∀ {μ c : ℝ}
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
      fderiv ℝ (fun x => f x * phaseRadialContact x (v 0)) (q 0) (w 0)) := by sorry
