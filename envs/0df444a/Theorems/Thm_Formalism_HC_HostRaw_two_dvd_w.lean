-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_two_dvd_w
-- name    : Formalism.HC.HostRaw.two_dvd_w
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:45.685717+00:00
-- url     : https://prove2.me/theorems/0163de00-a75f-48e7-b9d6-4b4fe5e60057
-- title:
--   Host Raw: two dvd w
-- statement:
--   The Host Raw construction uses the two dvd w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L67-L67

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

theorem Formalism.HC.HostRaw.two_dvd_w : 2 ∣ H.w := by sorry
