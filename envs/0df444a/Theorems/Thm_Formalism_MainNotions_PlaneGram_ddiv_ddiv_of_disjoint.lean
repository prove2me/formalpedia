-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_ddiv_of_disjoint
-- name    : Formalism.MainNotions.PlaneGram.ddiv_ddiv_of_disjoint
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:06:18.624074+00:00
-- url     : https://prove2.me/theorems/f1863e9c-0a7d-4ae2-a4ed-9c5dda15f0e6
-- title:
--   Plane Gram: ddiv ddiv of disjoint
-- statement:
--   The Plane Gram construction uses the ddiv ddiv of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L50-L62

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
variable {σ : Type} [Fintype σ]

theorem Formalism.MainNotions.PlaneGram.ddiv_ddiv_of_disjoint (M₁ M₂ : σ →₀ ℕ) (h : ∀ x, M₁ x = 0 ∨ M₂ x = 0)
    (F : MvPolynomial σ K) : ddiv M₁ (ddiv M₂ F) = ddiv (M₁ + M₂) F := by sorry
