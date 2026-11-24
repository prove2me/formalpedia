-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PsiP_ph
-- name    : Formalism.MainNotions.PlaneGram.TwistData.PsiP_ph
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:04:14.933819+00:00
-- url     : https://prove2.me/theorems/a769b475-df10-40b5-8d5d-787488ec366e
-- title:
--   Twist Data: Psi P ph
-- statement:
--   The Twist Data construction uses the Psi P ph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L60-L65

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

theorem Formalism.MainNotions.PlaneGram.TwistData.PsiP_ph (p : ℕ) {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) :
    D.ph p (D.PsiP j col occ) = rename (Prod.map (D.eA j) id) (∏ k, col k) := by sorry
