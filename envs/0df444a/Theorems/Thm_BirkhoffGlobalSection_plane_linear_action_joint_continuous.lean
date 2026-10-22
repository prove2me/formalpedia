-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_plane_linear_action_joint_continuous
-- name    : BirkhoffGlobalSection.plane_linear_action_joint_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:51:02.601986+00:00
-- url     : https://prove2.me/theorems/cfcdbab0-6120-44cd-b8f7-010009c05927
-- title:
--   Plane linear action joint continuous
-- statement:
--   A time-indexed real-linear plane action whose value on each fixed input vector is continuous in time has jointly continuous evaluation in time and input.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.contact_winding_interval_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_winding_interval_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_winding_interval_bundle

open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology

set_option maxHeartbeats 800000
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.plane_linear_action_joint_continuous :
∀ (A : ℝ → Plane → Plane)
    (hlin : ∀ t (p r : Plane) (a b : ℝ), A t (a • p + b • r) = a • A t p + b • A t r)
    (hcont : ∀ p, Continuous (fun t => A t p)),
    Continuous (fun x : ℝ × Plane => A x.1 x.2) := by sorry
