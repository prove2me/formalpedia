-- Prove2me | Theorems.Thm_Formalism_E_hermitian_tensor_mul_apply
-- name    : Formalism.E.hermitian_tensor_mul_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:23.0351+00:00
-- url     : https://prove2.me/theorems/bf6bbac3-f1a6-45c8-9386-19de83a05058
-- title:
--   E: hermitian tensor mul apply
-- statement:
--   The E construction uses the hermitian tensor mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/HermitianTensorMulHermitian.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/HermitianTensorMulHermitian.lean#L8-L10

import Definitions.Def_Formalism_FockGram_StatementTensor
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix LinearMap Module TensorProduct
noncomputable section
open Formalism Formalism.E

theorem Formalism.E.hermitian_tensor_mul_apply : HTmulApply := by sorry
