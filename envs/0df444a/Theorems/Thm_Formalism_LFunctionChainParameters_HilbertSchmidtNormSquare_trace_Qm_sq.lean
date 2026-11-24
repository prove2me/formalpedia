-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_Qm_sq
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trace_Qm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:36.687371+00:00
-- url     : https://prove2.me/theorems/021cae13-c61e-4e63-b450-d23672d1af35
-- title:
--   Hilbert Schmidt Norm Square: trace Qm sq
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the trace Qm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L66-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L66-L87

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
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trace_Qm_sq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ) := by sorry
