-- Prove2me | Theorems.Thm_Formalism_E_hermitian_tensor_mul_hermitian
-- name    : Formalism.E.hermitian_tensor_mul_hermitian
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:21.397358+00:00
-- url     : https://prove2.me/theorems/7f49ae54-cec4-4a24-bdbd-f70269aa6274
-- title:
--   E: hermitian tensor mul hermitian
-- statement:
--   The E construction uses the hermitian tensor mul hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/HermitianTensorMulHermitian.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/HermitianTensorMulHermitian.lean#L28-L41

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

theorem Formalism.E.hermitian_tensor_mul_hermitian : HTmulHerm := by sorry
