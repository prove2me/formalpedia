-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_dg
-- name    : Formalism.MainNotions.PlaneGram.TwistData.digitPart_dg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:04:23.772659+00:00
-- url     : https://prove2.me/theorems/9be280b6-9900-4f63-915e-d4e2f1cb2347
-- title:
--   Twist Data: digit Part dg
-- statement:
--   The Twist Data construction uses the digit Part dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L361-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L361-L368

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

theorem Formalism.MainNotions.PlaneGram.TwistData.digitPart_dg (ρ : D.Tau → Fin D.r → ℕ) (f : D.EA → K) (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ (dg f G) = dg (fun ζ => f (D.emb p ρ ζ)) (D.digitPart p ρ G) := by sorry
