-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_segStep_of
-- name    : Formalism.MainNotions.PlaneGram.segStep_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:08:20.505674+00:00
-- url     : https://prove2.me/theorems/6a34a195-6bc2-4cc3-aa50-7901b9b9af4c
-- title:
--   Plane Gram: seg Step of
-- statement:
--   The Plane Gram construction uses the seg Step of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L150-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L150-L197

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
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

theorem Formalism.MainNotions.PlaneGram.segStep_of {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
    (hS : SPAN K v p) : SegStep K v p := by sorry
