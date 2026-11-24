-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_isIntegral_trace_of_isIntegral
-- name    : Formalism.IrreducibleCountingLemmas.TW.isIntegral_trace_of_isIntegral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:31.573383+00:00
-- url     : https://prove2.me/theorems/7468698d-64c4-4dc0-a9de-42ab9fcc0f76
-- title:
--   TW: is Integral trace of is Integral
-- statement:
--   The TW construction uses the is Integral trace of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCentralIdempotentIntegral.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCentralIdempotentIntegral.lean#L7-L31

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCentralIdempotentIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.isIntegral_trace_of_isIntegral {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by sorry
