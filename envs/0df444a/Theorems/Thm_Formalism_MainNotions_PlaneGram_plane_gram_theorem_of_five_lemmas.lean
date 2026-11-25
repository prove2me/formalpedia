-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_plane_gram_theorem_of_five_lemmas
-- name    : Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_five_lemmas
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:49:42.337413+00:00
-- url     : https://prove2.me/theorems/cbff2a87-ad5a-492e-889c-ffe0972cc4a8
-- title:
--   Plane Gram: plane gram theorem of five lemmas
-- statement:
--   The Plane Gram construction uses the plane gram theorem of five lemmas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PlaneGramTheoremOfLemmas.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PlaneGramTheoremOfLemmas.lean#L13-L16

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

theorem Formalism.MainNotions.PlaneGram.plane_gram_theorem_of_five_lemmas (h1 : 1 ≤ C0) (hV2 : V2 K) (hSPAN : SPAN K v p) (hPROJ : PROJ K v p C0)
    (hDIG : DIG K v p) (hDER : DER K v p) : LiftBoundUniform K v p C0 := by sorry
