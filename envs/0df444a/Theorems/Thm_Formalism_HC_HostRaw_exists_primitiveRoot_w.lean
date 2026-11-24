-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_exists_primitiveRoot_w
-- name    : Formalism.HC.HostRaw.exists_primitiveRoot_w
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:54:59.91385+00:00
-- url     : https://prove2.me/theorems/59514e96-1e00-40ca-b5db-bc4bdd0ef137
-- title:
--   Host Raw: exists primitive Root w
-- statement:
--   The Host Raw construction uses the exists primitive Root w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L73-L73

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

theorem Formalism.HC.HostRaw.exists_primitiveRoot_w : ∃ ζ : H.E, IsPrimitiveRoot ζ H.w := by sorry
