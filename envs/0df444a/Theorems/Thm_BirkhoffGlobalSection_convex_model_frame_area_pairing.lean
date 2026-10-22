-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_frame_area_pairing
-- name    : BirkhoffGlobalSection.convex_model_frame_area_pairing
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:48:51.460985+00:00
-- url     : https://prove2.me/theorems/d3134257-4e44-4e6d-aa21-45adf58fbe30
-- title:
--   Convex model frame area pairing
-- statement:
--   At a sphere point, the displayed convex model normalized-frame combinations have weighted exterior pairing equal to the standard signed area of their plane coefficients.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_frame_area_pairing :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (p r : Plane),
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    (-phaseSymplecticForm (fderiv ℝ G u (p 0 • A + p 1 • B))
      (fderiv ℝ G u (r 0 • A + r 1 • B))) = p 0 * r 1 - p 1 * r 0 := by sorry
