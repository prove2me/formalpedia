-- Prove2me | Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_final_arith
-- name    : Formalism.NG.TrivialCharacterBlockLength.final_arith
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:39.907001+00:00
-- url     : https://prove2.me/theorems/ae52f38a-25f3-444a-ad57-dd8754df6143
-- title:
--   Trivial Character Block Length: final arith
-- statement:
--   The Trivial Character Block Length construction uses the final arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/BlockChiOneTriv.lean#L89-L93

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_final_arith

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

theorem Formalism.NG.TrivialCharacterBlockLength.final_arith (k X c vδ s R1 R2 : ℕ∞) (hk : k ≤ X + c * vδ) :
    k + (s + (R1 + R2)) ≤ s + X + R1 + 4 * (c + 1) * vδ + R2 := by sorry
