-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_gaR_one
-- name    : Formalism.MainNotions.PlaneGram.TwistData.gaR_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:05:19.212497+00:00
-- url     : https://prove2.me/theorems/648d463c-0f52-41c7-aef8-fa6574962129
-- title:
--   Twist Data: ga R one
-- statement:
--   The Twist Data construction uses the ga R one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L28-L30

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
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

theorem Formalism.MainNotions.PlaneGram.TwistData.gaR_one (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) :
    D.gaR p gam (D.labF ζ) 1 ζ = D.gaP p gam ζ := by sorry
