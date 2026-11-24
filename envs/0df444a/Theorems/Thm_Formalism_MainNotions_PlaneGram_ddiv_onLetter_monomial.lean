-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_onLetter_monomial
-- name    : Formalism.MainNotions.PlaneGram.ddiv_onLetter_monomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:06:29.133794+00:00
-- url     : https://prove2.me/theorems/6b53a0eb-2ce2-436c-8bcf-ab8db63e48d8
-- title:
--   Plane Gram: ddiv on Letter monomial
-- statement:
--   The Plane Gram construction uses the ddiv on Letter monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L249-L251

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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

theorem Formalism.MainNotions.PlaneGram.ddiv_onLetter_monomial (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    ddiv (onLetter i M) (monomial α (1 : K)) = putL i α (ddiv M (monomial (letE α i) 1)) := by sorry
