-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_eIn
-- name    : Formalism.MainNotions.PlaneGram.TwistData.pullE_eIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:06.960806+00:00
-- url     : https://prove2.me/theorems/2f47b319-2422-4820-a67a-abd0c7ba56ae
-- title:
--   Twist Data: pull E e In
-- statement:
--   The Twist Data construction uses the pull E e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L60-L64

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

theorem Formalism.MainNotions.PlaneGram.TwistData.pullE_eIn (ζ : D.EM) : D.pullE j (eIn (D.outSeg j) ζ) = D.pullE j ζ := by sorry
