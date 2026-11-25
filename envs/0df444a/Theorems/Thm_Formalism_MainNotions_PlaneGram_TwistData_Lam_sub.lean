-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_sub
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Lam_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:04.064998+00:00
-- url     : https://prove2.me/theorems/7407476e-015c-4053-9079-f8e653fa15a1
-- title:
--   Twist Data: Lam sub
-- statement:
--   The Twist Data construction uses the Lam sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L16-L18

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
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

theorem Formalism.MainNotions.PlaneGram.TwistData.Lam_sub (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (Z - W) = D.abelian₂ p F Z - D.abelian₂ p F W := by sorry
