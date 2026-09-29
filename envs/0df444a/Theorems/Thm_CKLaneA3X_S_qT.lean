-- Prove2me | Theorems.Thm_CKLaneA3X_S_qT
-- name    : CKLaneA3X.S_qT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T04:57:44.246479+00:00
-- url     : https://prove2.me/theorems/4825b539-91df-46dd-bd08-4a8c2baad1b6
-- title:
--   The A3X qT product has its stored enclosure
-- statement:
--   The exact original conditional source theorem: assuming Good F_q D_q and Good F_JJw2dR D_JJw2dR, the stored D_qT certificate encloses their product. The complete original analytic composition and every kernel-decided condition are retained.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step028.lean#L35

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions
import Definitions.Def_A3X_enclosure
import Definitions.Def_A3X_Step028_third_chain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.S_qT (G_q : Good F_q D_q) (G_JJw2dR : Good F_JJw2dR D_JJw2dR) : Good F_qT D_qT := by sorry
