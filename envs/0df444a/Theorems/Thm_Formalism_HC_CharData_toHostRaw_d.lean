-- Prove2me | Theorems.Thm_Formalism_HC_CharData_toHostRaw_d
-- name    : Formalism.HC.CharData.toHostRaw_d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:49.712095+00:00
-- url     : https://prove2.me/theorems/e6427be3-903c-4585-bc1d-94c0cbda2431
-- title:
--   Char Data: to Host Raw d
-- statement:
--   The Char Data construction uses the to Host Raw d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L142-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L142-L142

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

theorem Formalism.HC.CharData.toHostRaw_d : D.toHostRaw.d = D.d := by sorry
