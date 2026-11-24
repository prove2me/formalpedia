-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_le_of_sub_one
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_le_of_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:33.313284+00:00
-- url     : https://prove2.me/theorems/f87d0b59-58ff-478d-85f8-98f4a084868c
-- title:
--   Hilbert Schmidt Norm Square: hs Sq le of sub one
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq le of sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L187-L194

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_le_of_sub_one (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by sorry
