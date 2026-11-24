-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_X_fk
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ph_X_fk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:06:12.788796+00:00
-- url     : https://prove2.me/theorems/d292e188-4908-41ff-8ce3-84e6ac0fc1d8
-- title:
--   Twist Data: ph X fk
-- statement:
--   The Twist Data construction uses the ph X fk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L20-L29

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
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

theorem Formalism.MainNotions.PlaneGram.TwistData.ph_X_fk (p : ℕ) (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.fk j o l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by sorry
