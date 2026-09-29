-- Prove2me | Theorems.Thm_CKLaneA3X_S_mJwUsUs
-- name    : CKLaneA3X.S_mJwUsUs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:56:04.693163+00:00
-- url     : https://prove2.me/theorems/5c45d8de-34b3-486e-977b-119d1fc31f22
-- title:
--   Negating the A3X Jw times UsUs product preserves its certificate
-- statement:
--   The exact original conditional source theorem: assuming the Jw times UsUs product enclosure, its negative has the original stored certificate D_mJwUsUs. The source scaling proof and both kernel-decided numerical conditions are unchanged.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step028.lean#L17

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data
import Definitions.Def_A3X_Step027_data_functions
import Definitions.Def_A3X_enclosure
import Definitions.Def_A3X_Step028_first_chain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.S_mJwUsUs (G_JwUsUs : Good F_JwUsUs D_JwUsUs) : Good F_mJwUsUs D_mJwUsUs := by sorry
