-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_plane_gram_theorem_of_lemmas
-- name    : Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_lemmas
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:33.265289+00:00
-- url     : https://prove2.me/theorems/c2e473c5-ee41-40b7-ae01-945096423b34
-- title:
--   Plane Gram: plane gram theorem of lemmas
-- statement:
--   The Plane Gram construction uses the plane gram theorem of lemmas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PlaneGramTheoremOfLemmas.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PlaneGramTheoremOfLemmas.lean#L18-L20

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PlaneGramTheoremOfLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_lemmas : ∀ (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
    (C0 : ℝ), LiftBoundOfHypotheses K v p C0 := by sorry
