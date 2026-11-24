-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_all_parts_transfer_holds
-- name    : Formalism.IndefR.LatticeTransfer.all_parts_transfer_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:40.473801+00:00
-- url     : https://prove2.me/theorems/6424aa9c-ab1b-4e47-a718-32944f316c57
-- title:
--   Lattice Transfer: all parts transfer holds
-- statement:
--   The Lattice Transfer construction uses the all parts transfer holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/AllPartsTransferHolds.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/AllPartsTransferHolds.lean#L16-L16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer

theorem Formalism.IndefR.LatticeTransfer.all_parts_transfer_holds : AllPartsTransfer := by sorry
