-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_stepC_of
-- name    : Formalism.MainNotions.PlaneGram.stepC_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:08:21.307374+00:00
-- url     : https://prove2.me/theorems/055d29ea-3bf1-448b-9cee-118eb956bda4
-- title:
--   Plane Gram: step C of
-- statement:
--   The Plane Gram construction uses the step C of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L409-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L409-L426

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
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

theorem Formalism.MainNotions.PlaneGram.stepC_of [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} (hV2 : V2 K)
    (hSeg : SegStep K v p) : StepC K v p := by sorry
