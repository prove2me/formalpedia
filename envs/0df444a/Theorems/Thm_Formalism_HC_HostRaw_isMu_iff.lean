-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_isMu_iff
-- name    : Formalism.HC.HostRaw.isMu_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:35:07.966073+00:00
-- url     : https://prove2.me/theorems/2d4728b8-fe8a-4e00-aa16-75889bb605c1
-- title:
--   Host Raw: is Mu iff
-- statement:
--   The Host Raw construction uses the is Mu iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L71-L71

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.isMu_iff (x : H.E) : H.IsMu x ↔ x ^ H.w = 1 := by sorry
