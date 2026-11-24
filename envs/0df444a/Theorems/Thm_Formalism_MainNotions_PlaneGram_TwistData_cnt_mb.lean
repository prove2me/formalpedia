-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_mb
-- name    : Formalism.MainNotions.PlaneGram.TwistData.cnt_mb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:04:18.165264+00:00
-- url     : https://prove2.me/theorems/ae77f9e9-809e-4baa-b400-3e8016cae18d
-- title:
--   Twist Data: cnt mb
-- statement:
--   The Twist Data construction uses the cnt mb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L91-L93

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

theorem Formalism.MainNotions.PlaneGram.TwistData.cnt_mb (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.cnt j o (D.mb (D.eB j a)) = if Fin.castAdd D.r a ∈ o then 1 else 0 := by sorry
