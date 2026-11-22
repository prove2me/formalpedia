-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mlab
-- name    : Formalism.MainNotions.PlaneGram.TwistData.notSegL_mlab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:16.30536+00:00
-- url     : https://prove2.me/theorems/cf0904c8-5b45-42d6-beee-9cd59b7edf28
-- title:
--   Twist Data: not Seg L mlab
-- statement:
--   The Twist Data construction uses the not Seg L mlab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L94-L99

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
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.notSegL_mlab {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mlab (j', m)) := by sorry
