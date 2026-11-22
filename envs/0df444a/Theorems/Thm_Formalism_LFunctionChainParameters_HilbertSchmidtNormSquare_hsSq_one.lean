-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_one
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:49:26.901803+00:00
-- url     : https://prove2.me/theorems/2f387ac1-d1ef-4b1d-b53e-1ef59d3f61af
-- title:
--   Hilbert Schmidt Norm Square: hs Sq one
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L121-L126

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_one (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by sorry
