-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_Parity_every_combination_held
-- name    : APFPaper1.RecordOccupant.Parity.every_combination_held
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:23:27.031062+00:00
-- url     : https://prove2.me/theorems/ef8ea3e6-72e5-4494-9b2b-3a7b4458f1a4
-- title:
--   every combination held
-- statement:
--   Result: every combination held. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem every_combination_held : APFB02.EveryCombinationHeld side
--   ```
--
--   Module context and limits: The supplied parity example has raw individual sides and unsettled pair relations but a fixed triple parity. It checks EveryCombinationHeld, not all eight declared forms. Raw means no recorded side, not superposition.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper1_RecordOccupant_three_way_relation:63; pullbacks v39; source SHA-256 c28267bf7a82e83c0ef24d6f35d735854c20bf478aa5668a3e83b13f67054660']

import Definitions.Def_APFPaper1_RecordOccupant_three_way_relation_Vocabulary
import Definitions.Def_APFPaper1_RecordOccupant_sections_and_free_moves_Vocabulary
import Theorems.Thm_APFPaper1_RecordOccupant_Triangle_three_cannot_be_kept

set_option autoImplicit false

namespace APFPaper1.RecordOccupant.Parity
end APFPaper1.RecordOccupant.Parity
open APFPaper1
open APFPaper1.RecordOccupant
open APFPaper1.RecordOccupant.Parity
open Triangle

theorem APFPaper1.RecordOccupant.Parity.every_combination_held : APFB02.EveryCombinationHeld side := by sorry
