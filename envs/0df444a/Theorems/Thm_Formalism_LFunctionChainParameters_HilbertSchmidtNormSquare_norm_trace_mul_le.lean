-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_norm_trace_mul_le
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.norm_trace_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:39.869837+00:00
-- url     : https://prove2.me/theorems/1ff8207f-0bea-4ec6-8a7c-397718ea6ce0
-- title:
--   Hilbert Schmidt Norm Square: norm trace mul le
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the norm trace mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L108-L119

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.norm_trace_mul_le (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by sorry
