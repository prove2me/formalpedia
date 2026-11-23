-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_smul
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:35.919125+00:00
-- url     : https://prove2.me/theorems/b5b767c2-b452-4b2a-8e96-5e0506c7f2f8
-- title:
--   Hilbert Schmidt Norm Square: hs Sq smul
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L36-L37

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_smul (c : ℂ) (M : Matrix m n ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by sorry
