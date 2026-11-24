-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_traceLowerBound
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.traceLowerBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:07.876708+00:00
-- url     : https://prove2.me/theorems/914a36fb-f67a-496c-9c44-7d796aaea210
-- title:
--   Hilbert Schmidt Norm Square: trace Lower Bound
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the trace Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L137-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L137-L150

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.traceLowerBound : TraceLower := by sorry
