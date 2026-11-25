-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_sum_nuW_mul_log_le
-- name    : Formalism.HC.HostRaw.sum_nuW_mul_log_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:59.242834+00:00
-- url     : https://prove2.me/theorems/121189df-8b12-5d7a-85d9-5c89c8410fb2
-- title:
--   Host Raw: sum nu W mul log le
-- statement:
--   The Host Raw construction uses the sum nu W mul log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean#L85-L96

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

theorem Formalism.HC.HostRaw.sum_nuW_mul_log_le (S : Finset ℕ) : ∑ l ∈ S, (H.nuW l : ℝ) * Real.log l ≤ Real.log H.w := by sorry
