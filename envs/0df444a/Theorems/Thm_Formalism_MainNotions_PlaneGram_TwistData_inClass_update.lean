-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_inClass_update
-- name    : Formalism.MainNotions.PlaneGram.TwistData.inClass_update
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:05:02.625332+00:00
-- url     : https://prove2.me/theorems/9a81db14-798c-4a72-9a8f-c700a4170e8f
-- title:
--   Twist Data: in Class update
-- statement:
--   The Twist Data construction uses the in Class update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L414-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L414-L433

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

theorem Formalism.MainNotions.PlaneGram.TwistData.inClass_update (ρ'' : D.Tau → Fin D.r → ℕ) (α : D.EA) (cl : Fin D.r → ℕ) :
    D.InClass p (Function.update ρ'' t cl) α ↔
      (cl = fun a => α (Sum.inr t, a) % D.P p t) ∧
        ∀ t', t' ≠ t → ∀ a, α (Sum.inr t', a) % D.P p t' = ρ'' t' a := by sorry
