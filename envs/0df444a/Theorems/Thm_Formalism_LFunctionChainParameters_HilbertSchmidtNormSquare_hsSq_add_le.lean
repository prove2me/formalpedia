-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_add_le
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:18.408941+00:00
-- url     : https://prove2.me/theorems/9063d8c6-eebe-44b3-ac3c-7e66aface3c4
-- title:
--   Hilbert Schmidt Norm Square: hs Sq add le
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L162-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L162-L177

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {m n : Type} [Fintype m] [Fintype n]

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_add_le (A B : Matrix m n ℂ) : hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by sorry
