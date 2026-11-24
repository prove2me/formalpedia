-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_ram
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_ram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:34.622659+00:00
-- url     : https://prove2.me/theorems/d86962e3-dd07-4bcd-b335-dd4ab2c02eab
-- title:
--   Hilbert Schmidt Norm Square: num ram
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the num ram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L506-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L506-L514

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_ram {s a t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by sorry
