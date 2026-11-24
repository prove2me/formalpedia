-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_absE_letE
-- name    : Formalism.MainNotions.PlaneGram.absE_letE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:38.743677+00:00
-- url     : https://prove2.me/theorems/ef347776-2ab0-4760-80b8-78f71ea7898b
-- title:
--   Plane Gram: abs E let E
-- statement:
--   The Plane Gram construction uses the abs E let E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L113-L116

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
variable {L : Type} [DecidableEq L] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.absE_letE (α : L × Fin r →₀ ℕ) (i : L) : absE (letE α i) = ldeg α i := by sorry
