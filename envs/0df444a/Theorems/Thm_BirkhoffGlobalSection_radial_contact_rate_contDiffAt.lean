-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_contact_rate_contDiffAt
-- name    : BirkhoffGlobalSection.radial_contact_rate_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:15:18.449987+00:00
-- url     : https://prove2.me/theorems/2eab46e2-50eb-441a-af9d-9a5048d09818
-- title:
--   Radial contact rate contDiffAt
-- statement:
--   The radial contact pairing of a smooth phase-space vector field with the base point is smooth.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.model_contact_rate_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_model_contact_rate_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_contact_rate_contDiffAt :
∀ (X : Phase → Phase) (y : Phase)
    (hX : ContDiffAt ℝ ∞ X y),
    ContDiffAt ℝ ∞ (fun x => phaseRadialContact x (X x)) y := by sorry
