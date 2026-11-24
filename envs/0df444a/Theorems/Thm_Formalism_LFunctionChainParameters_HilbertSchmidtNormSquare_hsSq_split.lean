-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_split
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:11.097195+00:00
-- url     : https://prove2.me/theorems/5b59710e-f324-4604-be7a-72fd3b6d6790
-- title:
--   Hilbert Schmidt Norm Square: hs Sq split
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L300-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L300-L314

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_split (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by sorry
