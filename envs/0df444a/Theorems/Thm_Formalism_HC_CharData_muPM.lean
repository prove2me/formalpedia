-- Prove2me | Theorems.Thm_Formalism_HC_CharData_muPM
-- name    : Formalism.HC.CharData.muPM
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:23.556748+00:00
-- url     : https://prove2.me/theorems/0fc317ff-4a8c-4ba3-ab1f-472174003d6e
-- title:
--   Char Data: mu PM
-- statement:
--   The Char Data construction uses the mu PM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L150-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean#L150-L182

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

theorem Formalism.HC.CharData.muPM (h : ∀ k : ℕ, k ∣ D.QS * D.q * D.d →
    (∀ u : (ZMod (D.QS * D.q * D.d))ˣ, D.art u = 1 → (u : ZMod (D.QS * D.q * D.d)).val ≡ 1 [MOD k]) → k ∣ 2) :
    D.toHostRaw.MuPM := by sorry
