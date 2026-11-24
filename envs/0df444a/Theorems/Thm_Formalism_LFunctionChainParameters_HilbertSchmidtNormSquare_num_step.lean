-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_num_step
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:23.26299+00:00
-- url     : https://prove2.me/theorems/f9bac02a-dad5-4a16-a5b7-8f5ac55e9e38
-- title:
--   Hilbert Schmidt Norm Square: num step
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the num step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L519-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L519-L538

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_step {T2 T1 R Dst D X L c b : ℝ} (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst)
    (hX : 0 ≤ X) (hT2 : T2 ≤ R ^ 2 / Dst * X) (hb : 0 ≤ b * R) (hT1 : b * R ≤ T1)
    (hc : L * X ≤ c * b ^ 2) (hc0 : 0 ≤ c) : T2 ≤ c * T1 ^ 2 / D := by sorry
