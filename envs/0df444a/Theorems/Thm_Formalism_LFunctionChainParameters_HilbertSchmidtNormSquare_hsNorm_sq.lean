-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_sq
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:25.933055+00:00
-- url     : https://prove2.me/theorems/7f53513b-86fa-4611-8f0e-53427606f1ff
-- title:
--   Hilbert Schmidt Norm Square: hs Norm sq
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L159-L160

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
variable {m n : Type} [Fintype m] [Fintype n]

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_sq (M : Matrix m n ℂ) : hsNorm M ^ 2 = hsSq M := by sorry
