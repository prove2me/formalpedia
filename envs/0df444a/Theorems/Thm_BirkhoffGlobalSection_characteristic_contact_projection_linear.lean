-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_characteristic_contact_projection_linear
-- name    : BirkhoffGlobalSection.characteristic_contact_projection_linear
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:37:45.527989+00:00
-- url     : https://prove2.me/theorems/89a64a29-a24f-41ac-955c-fd6b5bf3afd8
-- title:
--   Characteristic contact projection linear
-- statement:
--   For fixed characteristic data, characteristic contact projection preserves arbitrary real linear combinations.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 3 of the Proved theorem BirkhoffGlobalSection.contact_frame_basis_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_contact_frame_basis_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.characteristic_contact_projection_linear :
∀ (F : Phase → ℝ) (y v w : Phase) (a b : ℝ),
    characteristicContactProjection F y (a • v + b • w) =
      a • characteristicContactProjection F y v + b • characteristicContactProjection F y w := by sorry
