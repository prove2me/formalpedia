-- Prove2me | Theorems.Thm_Formalism_NG_colKer
-- name    : Formalism.NG.colKer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:36.775503+00:00
-- url     : https://prove2.me/theorems/d58acc60-899d-4ee9-8f6a-78fcd232bf91
-- title:
--   NG: col Ker
-- statement:
--   The NG construction uses the col Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L93-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/ColKer.lean#L93-L200

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
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
open ColumnGeneratorDecomposition

theorem Formalism.NG.colKer : StatColKer := by sorry
