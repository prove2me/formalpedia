-- Prove2me | Theorems.Thm_Formalism_G0_TypeIIDownP_gb_one_one
-- name    : Formalism.G0.TypeIIDownP.gb_one_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:37:54.886036+00:00
-- url     : https://prove2.me/theorems/8a6c5ec6-236f-5720-9153-9c7f749848d7
-- title:
--   Type IIDown P: gb one one
-- statement:
--   The Type IIDown P construction uses the gb one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TypeIIDown.lean#L20-L20

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
open Formalism.G0.TypeIIDownP
open QVandermondeP

theorem Formalism.G0.TypeIIDownP.gb_one_one (q : ℕ) : gaussBinom q 1 1 = 1 := by sorry
