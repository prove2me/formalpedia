-- Prove2me | Theorems.Thm_Formalism_G0_typeIIDown_of
-- name    : Formalism.G0.typeIIDown_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:22.064977+00:00
-- url     : https://prove2.me/theorems/eeb55aad-9a1a-4005-a921-fa830eb9f7b9
-- title:
--   G0: type IIDown of
-- statement:
--   The G0 construction uses the type IIDown of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L233-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L233-L253

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open TypeIIDownP QVandermondeP

theorem Formalism.G0.typeIIDown_of (hS : SubspaceCount) : TypeIIDown := by sorry
