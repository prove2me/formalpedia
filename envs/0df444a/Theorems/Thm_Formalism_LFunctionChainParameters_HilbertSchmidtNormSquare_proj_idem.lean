-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_proj_idem
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.proj_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:42.283197+00:00
-- url     : https://prove2.me/theorems/ebf82aaa-98e1-46af-ab5a-c9ea05c4d3e9
-- title:
--   Hilbert Schmidt Norm Square: proj idem
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the proj idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L293-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L293-L298

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
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.proj_idem (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by sorry
