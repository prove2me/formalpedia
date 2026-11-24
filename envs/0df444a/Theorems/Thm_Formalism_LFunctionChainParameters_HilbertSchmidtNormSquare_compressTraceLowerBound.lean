-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressTraceLowerBound
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.compressTraceLowerBound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:03.621073+00:00
-- url     : https://prove2.me/theorems/168a62b7-809b-43c8-8e14-908b16b13125
-- title:
--   Hilbert Schmidt Norm Square: compress Trace Lower Bound
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the compress Trace Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L414-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L414-L448

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
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.compressTraceLowerBound : RamTrace := by sorry
