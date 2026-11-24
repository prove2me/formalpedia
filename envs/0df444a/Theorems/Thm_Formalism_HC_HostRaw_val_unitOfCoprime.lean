-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_val_unitOfCoprime
-- name    : Formalism.HC.HostRaw.val_unitOfCoprime
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:40.668799+00:00
-- url     : https://prove2.me/theorems/4b5d568b-f444-47af-b714-55a901a83153
-- title:
--   Host Raw: val unit Of Coprime
-- statement:
--   The Host Raw construction uses the val unit Of Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean#L185-L188

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.val_unitOfCoprime {p : ℕ} (h : Nat.Coprime p H.condN) :
    ((ZMod.unitOfCoprime p h : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ p [MOD H.condN] := by sorry
