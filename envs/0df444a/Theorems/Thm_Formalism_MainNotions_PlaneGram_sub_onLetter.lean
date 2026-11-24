-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_sub_onLetter
-- name    : Formalism.MainNotions.PlaneGram.sub_onLetter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:08:42.027357+00:00
-- url     : https://prove2.me/theorems/2d00cb19-8cb3-4942-8acb-0989060538bc
-- title:
--   Plane Gram: sub on Letter
-- statement:
--   The Plane Gram construction uses the sub on Letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L212-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L212-L219

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

theorem Formalism.MainNotions.PlaneGram.sub_onLetter (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    α - onLetter i M = offE i α + onLetter i (letE α i - M) := by sorry
