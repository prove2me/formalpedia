-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cge_digitPart
-- name    : Formalism.MainNotions.PlaneGram.TwistData.cge_digitPart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:05:28.340233+00:00
-- url     : https://prove2.me/theorems/8c897700-3f04-4b19-9b01-0ce8da4688bc
-- title:
--   Twist Data: cge digit Part
-- statement:
--   The Twist Data construction uses the cge digit Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L370-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L370-L379

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

theorem Formalism.MainNotions.PlaneGram.TwistData.cge_digitPart (v : AddValuation K (WithTop ℚ)) (ρ : D.Tau → Fin D.r → ℕ) {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (hG : cge v a G) : cge v a (D.digitPart p ρ G) := by sorry
