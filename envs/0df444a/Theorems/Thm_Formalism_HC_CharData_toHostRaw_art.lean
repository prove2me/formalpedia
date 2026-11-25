-- Prove2me | Theorems.Thm_Formalism_HC_CharData_toHostRaw_art
-- name    : Formalism.HC.CharData.toHostRaw_art
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:15.813267+00:00
-- url     : https://prove2.me/theorems/03999f39-8f05-4431-b9d2-0717efd5c531
-- title:
--   Char Data: to Host Raw art
-- statement:
--   The Char Data construction uses the to Host Raw art property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L144-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L144-L144

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

theorem Formalism.HC.CharData.toHostRaw_art : D.toHostRaw.art = D.art := by sorry
