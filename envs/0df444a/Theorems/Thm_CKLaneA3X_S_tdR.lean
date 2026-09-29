-- Prove2me | Theorems.Thm_CKLaneA3X_S_tdR
-- name    : CKLaneA3X.S_tdR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T04:20:38.143054+00:00
-- url     : https://prove2.me/theorems/1e25e50f-cc5f-4ba8-95b6-d9f66a7cf0a7
-- title:
--   Doubling the A3X dR product preserves its certificate
-- statement:
--   The exact original conditional source theorem: assuming the dR product enclosure, twice that function has the original stored D_tdR certificate. The source rational scaling by 2 and both numerical conditions are unchanged.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step028.lean#L29

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions
import Definitions.Def_A3X_enclosure
import Definitions.Def_A3X_Step028_second_chain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.S_tdR (G_dR : Good F_dR D_dR) : Good F_tdR D_tdR := by sorry
