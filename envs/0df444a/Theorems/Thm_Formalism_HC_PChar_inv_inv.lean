-- Prove2me | Theorems.Thm_Formalism_HC_PChar_inv_inv
-- name    : Formalism.HC.PChar.inv_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:00.737948+00:00
-- url     : https://prove2.me/theorems/4d4cd8db-a005-4904-aa95-83e828cc654a
-- title:
--   PChar: inv inv
-- statement:
--   The PChar construction uses the inv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean#L26-L30

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
attribute [instance] PChar.ne
open Formalism.HC.PChar

theorem Formalism.HC.PChar.inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by sorry
