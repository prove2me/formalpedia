-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_TL_preimage
-- name    : Formalism.MainNotions.PlaneGram.TwistData.TL_preimage
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:59.198347+00:00
-- url     : https://prove2.me/theorems/d9099732-3fbd-4ef8-901d-eab7f37f61a9
-- title:
--   Twist Data: TL preimage
-- statement:
--   The Twist Data construction uses the TL preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L135-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L135-L158

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

theorem Formalism.MainNotions.PlaneGram.TwistData.TL_preimage (m : Fin D.r) :
    (D.TLset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn = initSet (D.nB j + D.r) (D.stg j m) := by sorry
