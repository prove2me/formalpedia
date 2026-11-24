-- Prove2me | Theorems.Thm_Formalism_REAL_cartan_involution_conjTranspose_mul
-- name    : Formalism.REAL.cartan_involution_conjTranspose_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:20.95557+00:00
-- url     : https://prove2.me/theorems/20371ed3-ea09-44ed-be61-2c73c7b5670a
-- title:
--   REAL: cartan involution conj Transpose mul
-- statement:
--   The REAL construction uses the cartan involution conj Transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L114-L118

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.cartan_involution_conjTranspose_mul {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * Zᴴ * Jm ε)ᴴ * Jm ε = Jm ε * Z := by sorry
