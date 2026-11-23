-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inl
-- name    : Formalism.MainNotions.PlaneGram.TwistData.emb_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:14.049432+00:00
-- url     : https://prove2.me/theorems/0336b679-223b-4a33-a139-6f22981583c1
-- title:
--   Twist Data: emb inl
-- statement:
--   The Twist Data construction uses the emb inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L346-L348

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

theorem Formalism.MainNotions.PlaneGram.TwistData.emb_inl (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inl b, a) = ζ (D.mb b, a) := by sorry
