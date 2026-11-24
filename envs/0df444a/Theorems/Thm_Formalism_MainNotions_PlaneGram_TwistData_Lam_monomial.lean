-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_monomial
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Lam_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:16.269805+00:00
-- url     : https://prove2.me/theorems/db28b508-30b5-4164-a4ef-681b2f963cec
-- title:
--   Twist Data: Lam monomial
-- statement:
--   The Twist Data construction uses the Lam monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L24-L27

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
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

theorem Formalism.MainNotions.PlaneGram.TwistData.Lam_monomial (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) =
      F.coeff (D.phE p ζ) * (D.ga (D.phE p ζ) * c) * (fact (D.phE p ζ) : K) := by sorry
