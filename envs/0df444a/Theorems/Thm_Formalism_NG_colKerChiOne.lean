-- Prove2me | Theorems.Thm_Formalism_NG_colKerChiOne
-- name    : Formalism.NG.colKerChiOne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:15:20.209169+00:00
-- url     : https://prove2.me/theorems/347b74cc-8085-485f-8efd-578ec957a57b
-- title:
--   NG: col Ker Chi One
-- statement:
--   The NG construction uses the col Ker Chi One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKerChiOne.lean#L92-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKerChiOne.lean#L92-L161

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
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
open ColumnGeneratorDecomposition ColKerChi

theorem Formalism.NG.colKerChiOne : StatColKerChiOne := by sorry
