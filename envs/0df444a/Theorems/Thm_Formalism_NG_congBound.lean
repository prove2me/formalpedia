-- Prove2me | Theorems.Thm_Formalism_NG_congBound
-- name    : Formalism.NG.congBound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:46.074596+00:00
-- url     : https://prove2.me/theorems/5edb2a5b-2271-4b5e-a678-bc9371f54aef
-- title:
--   NG: cong Bound
-- statement:
--   The NG construction uses the cong Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L590-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean#L590-L603

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open QuotientPowerLengths

theorem Formalism.NG.congBound : StatCongBound := by sorry
