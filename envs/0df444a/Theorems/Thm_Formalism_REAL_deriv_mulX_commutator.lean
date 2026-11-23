-- Prove2me | Theorems.Thm_Formalism_REAL_deriv_mulX_commutator
-- name    : Formalism.REAL.deriv_mulX_commutator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:05.790827+00:00
-- url     : https://prove2.me/theorems/e21a66e0-513b-4eed-84bc-d888a6594528
-- title:
--   REAL: deriv mul X commutator
-- statement:
--   The REAL construction uses the deriv mul X commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L48-L55

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

theorem Formalism.REAL.deriv_mulX_commutator (v w : σ) : (D v) * (Mx w) - (Mx w) * (D v) = if v = w then 1 else 0 := by sorry
