-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_compress
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_compress
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:31.3806+00:00
-- url     : https://prove2.me/theorems/f09a13a2-0cb5-4a03-a55a-74cbd0e6db7a
-- title:
--   Hilbert Schmidt Norm Square: hs Sq compress
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the hs Sq compress property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L324-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L324-L330

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_compress {a b c e : ℕ} (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1) (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by sorry
