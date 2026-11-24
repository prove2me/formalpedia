-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_rename
-- name    : Formalism.MainNotions.PlaneGram.cge_rename
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:49.625221+00:00
-- url     : https://prove2.me/theorems/8dc6a61c-8f01-4bc5-99f2-aba7cc4dce03
-- title:
--   Plane Gram: cge rename
-- statement:
--   The Plane Gram construction uses the cge rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L221-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L221-L229

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.cge_rename (v : AddValuation K (WithTop ℚ)) {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)
    {a : ℝ} {Q : MvPolynomial σ K} (hQ : cge v a Q) : cge v a (rename f Q) := by sorry
