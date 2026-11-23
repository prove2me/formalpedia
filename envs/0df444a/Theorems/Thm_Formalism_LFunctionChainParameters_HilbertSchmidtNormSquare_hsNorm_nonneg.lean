-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_nonneg
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:22.696559+00:00
-- url     : https://prove2.me/theorems/47a52809-1727-43ff-bff4-e2283a81f8b1
-- title:
--   Hilbert Schmidt Norm Square: hs Norm nonneg
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Norm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L156-L157

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ hsNorm M := by sorry
