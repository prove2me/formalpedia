-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_vdH_nonneg
-- name    : Formalism.HC.HostRaw.vdH_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:39.6195+00:00
-- url     : https://prove2.me/theorems/7a08a96a-0f5b-4fd7-a9db-a68b927f4dbe
-- title:
--   Host Raw: vd H nonneg
-- statement:
--   The Host Raw construction uses the vd H nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SlopeTestRemainingChoices.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/SlopeTestRemainingChoices.lean#L32-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.vdH_nonneg (p : ℕ) : 0 ≤ H.vdH p := by sorry
