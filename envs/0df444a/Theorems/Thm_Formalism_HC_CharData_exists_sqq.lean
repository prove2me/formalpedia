-- Prove2me | Theorems.Thm_Formalism_HC_CharData_exists_sqq
-- name    : Formalism.HC.CharData.exists_sqq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:38.321562+00:00
-- url     : https://prove2.me/theorems/51ee7da2-2796-49d7-a62b-aa1a5d072f36
-- title:
--   Char Data: exists sqq
-- statement:
--   The Char Data construction uses the exists sqq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L146-L148

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

theorem Formalism.HC.CharData.exists_sqq (h : D.toHostRaw.PsQ) : ∃ s : D.toHostRaw.E, s ^ 2 = -(D.toHostRaw.q : D.toHostRaw.E) ∧
    ∀ σ : D.toHostRaw.E ≃ₐ[ℚ] D.toHostRaw.E, σ s = ((((D.toHostRaw.gal σ).1.1 : ℤˣ) : ℤ) : D.toHostRaw.E) * s := by sorry
