-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_smul
-- name    : Formalism.MainNotions.PlaneGram.ddiv_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:06:27.8748+00:00
-- url     : https://prove2.me/theorems/e1427235-67fc-4c1d-aff4-a6c6a749f242
-- title:
--   Plane Gram: ddiv smul
-- statement:
--   The Plane Gram construction uses the ddiv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L53-L54

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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

theorem Formalism.MainNotions.PlaneGram.ddiv_smul {σ : Type} (M : σ →₀ ℕ) (a : K) (F : MvPolynomial σ K) :
    ddiv M (a • F) = a • ddiv M F := by sorry
