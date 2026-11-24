-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_substitution_X_first_embedding
-- name    : Formalism.MainNotions.PlaneGram.TwistData.substitution_X_first_embedding
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:06:45.891432+00:00
-- url     : https://prove2.me/theorems/7dbc5f97-1823-4cf4-adcf-f3b91571b028
-- title:
--   Twist Data: substitution X first embedding
-- statement:
--   The Twist Data construction uses the substitution X first embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L31-L37

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

theorem Formalism.MainNotions.PlaneGram.TwistData.substitution_X_first_embedding (p : ℕ) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.e0 j l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by sorry
