-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_zero
-- name    : Formalism.MainNotions.PlaneGram.TwistData.cnt_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:30.435741+00:00
-- url     : https://prove2.me/theorems/36380916-dd74-49a8-adec-6b2c79b4d763
-- title:
--   Twist Data: cnt zero
-- statement:
--   The Twist Data construction uses the cnt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L49-L52

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

theorem Formalism.MainNotions.PlaneGram.TwistData.cnt_zero (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (h : ∀ l, D.fk j o l ≠ i) :
    D.cnt j o i = 0 := by sorry
