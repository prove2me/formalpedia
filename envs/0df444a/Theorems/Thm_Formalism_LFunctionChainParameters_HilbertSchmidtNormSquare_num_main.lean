-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_main
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:12.206623+00:00
-- url     : https://prove2.me/theorems/0c028725-09c6-480e-8d0b-f3b5a8d8c952
-- title:
--   Hilbert Schmidt Norm Square: num main
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the num main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L481-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L481-L502

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
set_option maxHeartbeats 800000

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_main {s η0 η1 a : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1' : η1 ≤ s / 2) (_hL : 0 ≤ 1 + η1) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by sorry
