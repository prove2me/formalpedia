-- Prove2me | Theorems.Thm_Formalism_YangianSpanCharacter_Final_E_GGProd
-- name    : Formalism.YangianSpanCharacter.Final.E_GGProd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:30:45.336264+00:00
-- url     : https://prove2.me/theorems/19d15e28-bd4f-4c07-a2c9-121e4028090f
-- title:
--   Final: E GGProd
-- statement:
--   The Final construction uses the E GGProd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRelationFirst.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRelationFirst.lean#L18-L18

import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeSymplecticShift
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SpanCharacterIdentity
import Definitions.Def_Formalism_YangianSpanCharacter_ModHypYangian
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_MinusFrameIdentity
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJReversed
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_TransposeJTransposeReal
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.Final

theorem Formalism.YangianSpanCharacter.Final.E_GGProd : Formalism.YangianSpanCharacter.E.GGProd := by sorry
