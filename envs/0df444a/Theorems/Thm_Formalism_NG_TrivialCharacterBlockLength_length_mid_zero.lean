-- Prove2me | Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_length_mid_zero
-- name    : Formalism.NG.TrivialCharacterBlockLength.length_mid_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:52.111264+00:00
-- url     : https://prove2.me/theorems/c1dac497-81df-46f8-877e-739f0a8aed81
-- title:
--   Trivial Character Block Length: length mid zero
-- statement:
--   The Trivial Character Block Length construction uses the length mid zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L17-L31

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.TrivialCharacterBlockLength
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

theorem Formalism.NG.TrivialCharacterBlockLength.length_mid_zero {H : Type*} [AddCommGroup H] [Module O H] (ρM : Representation O G M)
    (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) = 0 := by sorry
