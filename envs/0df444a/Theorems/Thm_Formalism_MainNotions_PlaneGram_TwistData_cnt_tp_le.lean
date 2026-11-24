-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_tp_le
-- name    : Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:03:48.464518+00:00
-- url     : https://prove2.me/theorems/7731bdf9-adc1-4f8d-85a6-ff40029f21e6
-- title:
--   Twist Data: cnt tp le
-- statement:
--   The Twist Data construction uses the cnt tp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L124-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L124-L142

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

theorem Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_le (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mtp (j, m)) ≤ ∑ a : Fin (D.nB j), if Fin.castAdd D.r a ∈ o then 1 else 0 := by sorry
