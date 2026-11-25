-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_w_dvd_condN
-- name    : Formalism.HC.HostRaw.w_dvd_condN
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:35:20.792779+00:00
-- url     : https://prove2.me/theorems/452c9197-1068-449a-90f3-32e660e83f82
-- title:
--   Host Raw: w dvd cond N
-- statement:
--   The Host Raw construction uses the w dvd cond N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L82-L83

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

theorem Formalism.HC.HostRaw.w_dvd_condN : H.w ∣ H.condN := by sorry
