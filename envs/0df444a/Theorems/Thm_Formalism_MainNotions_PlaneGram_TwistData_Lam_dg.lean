-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_dg
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Lam_dg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:19.348806+00:00
-- url     : https://prove2.me/theorems/8253103f-e1e1-4e27-be7b-58a53198abfa
-- title:
--   Twist Data: Lam dg
-- statement:
--   The Twist Data construction uses the Lam dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L215-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L215-L220

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.Lam_dg (F : MvPolynomial (D.OL × Fin D.r) K) (g : D.EM → K) (W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (dg g W) = ∑ ζ ∈ W.support, g ζ * W.coeff ζ * D.abelian₂ p F (monomial ζ 1) := by sorry
