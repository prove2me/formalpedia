-- Prove2me | Theorems.Thm_APFPaper1_RecordOccupant_Parity_members_raw
-- name    : APFPaper1.RecordOccupant.Parity.members_raw
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:24:53.946785+00:00
-- url     : https://prove2.me/theorems/6be49127-6ed8-4678-8f34-ded7629bfbb9
-- title:
--   members raw
-- statement:
--   Result: members raw. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem members_raw (d : Corner) : NoSide side odd ({()} : Finset Unit) d
--   ```
--
--   Module context and limits: The supplied parity example has raw individual sides and unsettled pair relations but a fixed triple parity. It checks EveryCombinationHeld, not all eight declared forms. Raw means no recorded side, not superposition.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper1_RecordOccupant_three_way_relation:67; pullbacks v39; source SHA-256 c28267bf7a82e83c0ef24d6f35d735854c20bf478aa5668a3e83b13f67054660']

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

theorem APFPaper1.RecordOccupant.Parity.members_raw (d : Corner) : NoSide side odd ({()} : Finset Unit) d := by sorry
