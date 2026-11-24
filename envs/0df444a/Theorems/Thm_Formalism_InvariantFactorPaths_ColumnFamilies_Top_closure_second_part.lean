-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_Top_closure_second_part
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_second_part
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:59.284638+00:00
-- url     : https://prove2.me/theorems/e274ec10-69f9-4a44-90f8-46f75297171a
-- title:
--   Top: closure second part
-- statement:
--   The Top construction uses the closure second part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/ClosureSecondPart.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/ClosureSecondPart.lean#L14-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_ClosureSecondPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies Formalism.InvariantFactorPaths.ColumnFamilies.Top

theorem Formalism.InvariantFactorPaths.ColumnFamilies.Top.closure_second_part : ClosureTensorPowers := by sorry
