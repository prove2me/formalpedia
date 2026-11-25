-- Prove2me | Theorems.Thm_Formalism_HC_CharData_toHostRaw_QS
-- name    : Formalism.HC.CharData.toHostRaw_QS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:27.88184+00:00
-- url     : https://prove2.me/theorems/c246e982-75d9-4f73-8968-236a968cbce3
-- title:
--   Char Data: to Host Raw QS
-- statement:
--   The Char Data construction uses the to Host Raw QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L143-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L143-L143

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.CharData
variable {φ : Frame} (D : CharData φ)

theorem Formalism.HC.CharData.toHostRaw_QS : D.toHostRaw.QS = D.QS := by sorry
