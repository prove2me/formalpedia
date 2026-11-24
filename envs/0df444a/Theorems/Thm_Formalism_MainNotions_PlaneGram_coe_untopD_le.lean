-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coe_untopD_le
-- name    : Formalism.MainNotions.PlaneGram.coe_untopD_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:07:07.381943+00:00
-- url     : https://prove2.me/theorems/6b00e98e-af09-4383-89ff-ad1a7a503ee8
-- title:
--   Plane Gram: coe untop D le
-- statement:
--   The Plane Gram construction uses the coe untop D le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/RenamePullLCoefOut.lean#L9-L12

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

theorem Formalism.MainNotions.PlaneGram.coe_untopD_le (x : WithTop ℤ) : ((x.untopD 0 : ℤ) : WithTop ℤ) ≤ x := by sorry
