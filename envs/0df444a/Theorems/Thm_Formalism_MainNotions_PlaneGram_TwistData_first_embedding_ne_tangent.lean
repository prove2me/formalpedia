-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_first_embedding_ne_tangent
-- name    : Formalism.MainNotions.PlaneGram.TwistData.first_embedding_ne_tangent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:11.375419+00:00
-- url     : https://prove2.me/theorems/023d3f1b-17bf-4703-81cb-e408ef728f05
-- title:
--   Twist Data: first embedding ne tangent
-- statement:
--   The Twist Data construction uses the first embedding ne tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L62-L63

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

theorem Formalism.MainNotions.PlaneGram.TwistData.first_embedding_ne_tangent (l : Fin (D.nB j + D.r)) (t : D.Tau) : D.e0 j l ≠ D.mtp t := by sorry
