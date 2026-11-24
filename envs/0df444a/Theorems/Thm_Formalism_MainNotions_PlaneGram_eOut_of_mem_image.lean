-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_of_mem_image
-- name    : Formalism.MainNotions.PlaneGram.eOut_of_mem_image
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:06:23.772839+00:00
-- url     : https://prove2.me/theorems/4e9f8218-04d9-4c9f-8a70-e91906d034a4
-- title:
--   Plane Gram: e Out of mem image
-- statement:
--   The Plane Gram construction uses the e Out of mem image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L93-L97

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

theorem Formalism.MainNotions.PlaneGram.eOut_of_mem_image {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out]
    (F : MvPolynomial (L × Fin r) K) {μ : L × Fin r →₀ ℕ} (hμ : μ ∈ F.support.image (eOut out)) :
    eOut out μ = μ := by sorry
