-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_conjTranspose_mul_self
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trace_conjTranspose_mul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:30.671823+00:00
-- url     : https://prove2.me/theorems/47f44d6c-9489-437b-ad25-8ea19e71b754
-- title:
--   Hilbert Schmidt Norm Square: trace conj Transpose mul self
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the trace conj Transpose mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L22-L27

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
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = ((hsSq M : ℝ) : ℂ) := by sorry
