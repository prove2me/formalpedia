-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_vdH_le_natAbs
-- name    : Formalism.HC.HostRaw.vdH_le_natAbs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:38.477801+00:00
-- url     : https://prove2.me/theorems/9810db74-95b5-4a29-b793-e61f81c38bc2
-- title:
--   Host Raw: vd H le nat Abs
-- statement:
--   The Host Raw construction uses the vd H le nat Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/VdHLeNatAbs.lean#L4-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/VdHLeNatAbs.lean#L4-L11

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_VdHLeNatAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem Formalism.HC.HostRaw.vdH_le_natAbs {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) :
    H.vdH p ≤ ((NumberField.discr H.E).natAbs : ℝ) := by sorry
