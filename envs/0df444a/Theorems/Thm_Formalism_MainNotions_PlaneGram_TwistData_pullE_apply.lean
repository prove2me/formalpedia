-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_apply
-- name    : Formalism.MainNotions.PlaneGram.TwistData.pullE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:53.455853+00:00
-- url     : https://prove2.me/theorems/3125878a-1e5a-4b3f-bb93-65576758b28a
-- title:
--   Twist Data: pull E apply
-- statement:
--   The Twist Data construction uses the pull E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L29-L31

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem Formalism.MainNotions.PlaneGram.TwistData.pullE_apply (ζ : D.EM) (k : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.pullE j ζ (k, a) = ζ (D.e0 j k, a) := by sorry
