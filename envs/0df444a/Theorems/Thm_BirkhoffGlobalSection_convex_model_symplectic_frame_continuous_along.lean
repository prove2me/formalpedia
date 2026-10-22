-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_symplectic_frame_continuous_along
-- name    : BirkhoffGlobalSection.convex_model_symplectic_frame_continuous_along
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:38.297984+00:00
-- url     : https://prove2.me/theorems/eb2a7d4b-c3d6-4f18-9888-db71384b63b8
-- title:
--   Convex model symplectic frame continuous along
-- statement:
--   Pulling either global convex model symplectic contact-frame vector back along a continuous sphere-valued map gives a continuous vector-valued map.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 9 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_convex_model_symplectic_frame_continuous_along

theorem BirkhoffGlobalSection.convex_model_symplectic_frame_continuous_along :
∀ {A : Type u_convex_model_symplectic_frame_continuous_along} [TopologicalSpace A]
    {μ c : ℝ} (M : ConvexRegularizationModel μ c) (d : A → Phase)
    (hd : Continuous d) (hs : ∀ z, d z ∈ unitThreeSphere) (i : Fin 2),
    Continuous (fun z => convexModelSymplecticContactFrame M (d z) i) := by sorry
