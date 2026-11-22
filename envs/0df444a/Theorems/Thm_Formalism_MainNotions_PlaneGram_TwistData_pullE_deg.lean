-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_deg
-- name    : Formalism.MainNotions.PlaneGram.TwistData.pullE_deg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:47.672796+00:00
-- url     : https://prove2.me/theorems/953f1bb4-3090-4f23-9898-f2758ceade27
-- title:
--   Twist Data: pull E deg
-- statement:
--   The Twist Data construction uses the pull E deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L66-L76

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

theorem Formalism.MainNotions.PlaneGram.TwistData.pullE_deg (ζ : D.EM) (h : D.PreE j ζ) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = D.dO (D.eA j k) := by sorry
