-- Prove2me | Theorems.Thm_Formalism_REAL_mulX_mul_mulX_comm
-- name    : Formalism.REAL.mulX_mul_mulX_comm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:31.093019+00:00
-- url     : https://prove2.me/theorems/8c6c52bc-cc84-4032-b151-46a6e41e91b1
-- title:
--   REAL: mul X mul mul X comm
-- statement:
--   The REAL construction uses the mul X mul mul X comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L71-L74

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {σ : Type*} [DecidableEq σ]
set_option quotPrecheck false
local notation "D" v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap :
  Module.End ℂ (MvPolynomial σ ℂ))
local notation "Mx" v => (LinearMap.mulLeft ℂ (X v : MvPolynomial σ ℂ) : Module.End ℂ (MvPolynomial σ ℂ))

theorem Formalism.REAL.mulX_mul_mulX_comm (v w : σ) : (Mx v) * (Mx w) = (Mx w) * (Mx v) := by sorry
