-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_inClass_new
-- name    : Formalism.MainNotions.PlaneGram.TwistData.inClass_new
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:05:17.32697+00:00
-- url     : https://prove2.me/theorems/f15643cc-50cb-4d8c-98da-3034e7b09473
-- title:
--   Twist Data: in Class new
-- statement:
--   The Twist Data construction uses the in Class new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L383-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L383-L412

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

theorem Formalism.MainNotions.PlaneGram.TwistData.inClass_new (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (ρ1 x : Fin D.r →₀ ℕ) :
    D.InClass p ρ'' (offE (Sum.inr t) α + onLetter (Sum.inr t) (ρ1 + D.P p t • x)) ↔
      (∀ a, ρ1 a % D.P p t = ρ'' t a) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by sorry
