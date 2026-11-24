-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_absE_eq_sum
-- name    : Formalism.MainNotions.PlaneGram.absE_eq_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:48.805058+00:00
-- url     : https://prove2.me/theorems/2cb8cea2-e6bb-4849-b08a-6eae57327e0e
-- title:
--   Plane Gram: abs E eq sum
-- statement:
--   The Plane Gram construction uses the abs E eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L109-L111

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

theorem Formalism.MainNotions.PlaneGram.absE_eq_sum (β : Fin r →₀ ℕ) : absE β = ∑ a, β a := by sorry
