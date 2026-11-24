-- Prove2me | Theorems.Thm_Formalism_REAL_deriv_mul_mulX_comm_of_ne
-- name    : Formalism.REAL.deriv_mul_mulX_comm_of_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:45.433878+00:00
-- url     : https://prove2.me/theorems/da08ea28-370b-47a4-bd5e-be2581cd8ed8
-- title:
--   REAL: deriv mul mul X comm of ne
-- statement:
--   The REAL construction uses the deriv mul mul X comm of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L76-L79

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

theorem Formalism.REAL.deriv_mul_mulX_comm_of_ne {v w : σ} (h : v ≠ w) : (D v) * (Mx w) = (Mx w) * (D v) := by sorry
