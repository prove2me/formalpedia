-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_characteristic_contact_projection_contDiffAt
-- name    : BirkhoffGlobalSection.characteristic_contact_projection_contDiffAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:39:27.326998+00:00
-- url     : https://prove2.me/theorems/3a204e2c-0bf8-4ba6-88e4-93c49a61cee9
-- title:
--   Characteristic contact projection contDiffAt
-- statement:
--   Characteristic contact projection is smooth in its base-point data wherever those data are smooth and the radial denominator is nonzero.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.characteristic_contact_projection_contDiffAt :
∀ (F : Phase → ℝ) (V : Phase → Phase)
    (y : Phase) (hF : ContDiffAt ℝ ∞ F y) (hV : ContDiffAt ℝ ∞ V y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    ContDiffAt ℝ ∞ (fun z => characteristicContactProjection F z (V z)) y := by sorry
