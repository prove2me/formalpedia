-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_plane_gram_theorem_of_combined_lemmas
-- name    : Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_combined_lemmas
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:07:29.815841+00:00
-- url     : https://prove2.me/theorems/b7d93360-ebb4-44fc-bd11-f896e1403a46
-- title:
--   Plane Gram: plane gram theorem of combined lemmas
-- statement:
--   The Plane Gram construction uses the plane gram theorem of combined lemmas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L97-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/TestBoundOfRhoAndNormSets.lean#L97-L156

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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_combined_lemmas (h1 : 1 ≤ C0) (hBC : StepBC K v p C0) (hDEF : StepDEF K v p C0) :
    LiftBoundUniform K v p C0 := by sorry
