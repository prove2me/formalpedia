-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_global_frame_extends_over_capping_disk
-- name    : BirkhoffGlobalSection.convex_model_global_frame_extends_over_capping_disk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:43:41.501481+00:00
-- url     : https://prove2.me/theorems/3d7a3c4d-0252-4bbb-93b3-b9d186db9cba
-- title:
--   Convex model global frame extends over capping disk
-- statement:
--   For a supplied continuous sphere-valued capping disk, the global convex model frame restricts to the displayed continuous frame over the disk and agrees with its boundary frame. A capping disk is supplied, not constructed.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained. This is a conditional result for the defined convex regularization model, not a global-section or index-existence theorem.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.contact_frame_angle_disk_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_angle_disk_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.convex_model_global_frame_extends_over_capping_disk :
∀ {μ c : ℝ}
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
      (∀ z i, E z.val i = convexModelSymplecticContactFrame M (γ z) i) := by sorry
