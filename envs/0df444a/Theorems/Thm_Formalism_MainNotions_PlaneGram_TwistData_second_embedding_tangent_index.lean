-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_second_embedding_tangent_index
-- name    : Formalism.MainNotions.PlaneGram.TwistData.second_embedding_tangent_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:46.302366+00:00
-- url     : https://prove2.me/theorems/74f9f79e-387e-4289-8187-20c4f6d7ff8c
-- title:
--   Twist Data: second embedding tangent index
-- statement:
--   The Twist Data construction uses the second embedding tangent index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L65-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L65-L76

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
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

theorem Formalism.MainNotions.PlaneGram.TwistData.second_embedding_tangent_index (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mtp (j, m)) :
    m.val ≠ 0 ∧ l = Fin.natAdd (D.nB j) (Fin.rev m) := by sorry
