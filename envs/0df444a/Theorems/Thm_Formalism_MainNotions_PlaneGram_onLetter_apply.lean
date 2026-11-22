-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
-- name    : Formalism.MainNotions.PlaneGram.onLetter_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:40.779746+00:00
-- url     : https://prove2.me/theorems/3551618f-65c1-4252-b64b-d03e5a2c182c
-- title:
--   Plane Gram: on Letter apply
-- statement:
--   The Plane Gram construction uses the on Letter apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L82-L95

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

theorem Formalism.MainNotions.PlaneGram.onLetter_apply (i : L) (β : Fin r →₀ ℕ) (j : L) (a : Fin r) :
    onLetter i β (j, a) = if j = i then β a else 0 := by sorry
