-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_seg_eB
-- name    : Formalism.MainNotions.PlaneGram.TwistData.seg_eB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:40.409827+00:00
-- url     : https://prove2.me/theorems/5d5aec12-d7ef-40c1-b5f9-248cca5a04d3
-- title:
--   Twist Data: seg e B
-- statement:
--   The Twist Data construction uses the seg e B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L20-L24

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
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

theorem Formalism.MainNotions.PlaneGram.TwistData.seg_eB (a : Fin (D.nB j)) : D.seg (D.eB j a) = j := by sorry
