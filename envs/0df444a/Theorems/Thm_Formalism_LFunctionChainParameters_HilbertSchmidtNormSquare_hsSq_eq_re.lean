-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_eq_re
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_eq_re
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:19.899645+00:00
-- url     : https://prove2.me/theorems/baa93386-838d-4037-b09f-2cfe13ea2636
-- title:
--   Hilbert Schmidt Norm Square: hs Sq eq re
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq eq re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L29-L30

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_eq_re (M : Matrix m n ℂ) : hsSq M = (Mᴴ * M).trace.re := by sorry
