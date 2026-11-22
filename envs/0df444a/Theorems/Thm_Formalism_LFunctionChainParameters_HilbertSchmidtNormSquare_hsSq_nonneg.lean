-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_nonneg
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:34.937806+00:00
-- url     : https://prove2.me/theorems/dc226549-bdc7-4e1d-9754-facfa03bb92f
-- title:
--   Hilbert Schmidt Norm Square: hs Sq nonneg
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L14-L16

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M := by sorry
