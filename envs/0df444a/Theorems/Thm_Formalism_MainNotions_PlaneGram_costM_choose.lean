-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_costM_choose
-- name    : Formalism.MainNotions.PlaneGram.costM_choose
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:07:07.745604+00:00
-- url     : https://prove2.me/theorems/901a5b4e-2a96-42f2-a9b6-b5473606968d
-- title:
--   Plane Gram: cost M choose
-- statement:
--   The Plane Gram construction uses the cost M choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L47-L51

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.costM_choose (hV2 : V2 K) (D : TwistData K) (hr : 0 < D.r) (x : D.ML × Fin D.r) (k : ℕ) :
    CostM D k (fun α => ((α x).choose k : K)) := by sorry
