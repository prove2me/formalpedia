-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_new
-- name    : Formalism.MainNotions.PlaneGram.TwistData.liftE_new
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:05:22.328887+00:00
-- url     : https://prove2.me/theorems/42f91e99-c091-4368-858c-445501c7597d
-- title:
--   Twist Data: lift E new
-- statement:
--   The Twist Data construction uses the lift E new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L440-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L440-L456

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)

theorem Formalism.MainNotions.PlaneGram.TwistData.liftE_new (hP : 0 < D.P p t) (α : D.EA) (ρ1 δ1 κ1 : Fin D.r →₀ ℕ) :
    D.liftE p (offE (Sum.inr t) α + onLetter (Sum.inr t)
        (ρ1 + D.P p t • (δ1 + (divE (D.P p t) (letE α (Sum.inr t)) - κ1)))) =
      onLetter (D.mw t) (divE (D.P p t) ρ1 + δ1) + (D.liftE p α - onLetter (D.mw t) κ1) := by sorry
