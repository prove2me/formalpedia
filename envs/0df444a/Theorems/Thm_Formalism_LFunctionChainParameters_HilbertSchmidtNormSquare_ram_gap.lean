-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_ram_gap
-- name    : Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.ram_gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:28.92178+00:00
-- url     : https://prove2.me/theorems/36379a94-bef2-4ed0-a30b-cdb693bd0c3f
-- title:
--   Hilbert Schmidt Norm Square: ram gap
-- statement:
--   The Hilbert Schmidt Norm Square construction uses the ram gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L360-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TraceConjTransposeMulSelf.lean#L360-L395

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

theorem Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.ram_gap (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0) (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧
    K.trace.re - (Vᴴ * K * V).trace.re
      ≤ ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by sorry
