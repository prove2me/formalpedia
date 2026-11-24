-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_smul
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Lam_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:04:02.058403+00:00
-- url     : https://prove2.me/theorems/274620ab-a476-4bdc-8736-b71cfdf76a08
-- title:
--   Twist Data: Lam smul
-- statement:
--   The Twist Data construction uses the Lam smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L20-L22

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

theorem Formalism.MainNotions.PlaneGram.TwistData.Lam_smul (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (a : K) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (a • Z) = a * D.abelian₂ p F Z := by sorry
