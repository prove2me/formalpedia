-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inr
-- name    : Formalism.MainNotions.PlaneGram.TwistData.emb_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:11.547104+00:00
-- url     : https://prove2.me/theorems/70099c18-d28d-4a6d-9a1d-3966102f8cba
-- title:
--   Twist Data: emb inr
-- statement:
--   The Twist Data construction uses the emb inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L350-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L350-L352

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

theorem Formalism.MainNotions.PlaneGram.TwistData.emb_inr (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inr t, a) = ρ t a + D.P p t * ζ (D.mw t, a) := by sorry
