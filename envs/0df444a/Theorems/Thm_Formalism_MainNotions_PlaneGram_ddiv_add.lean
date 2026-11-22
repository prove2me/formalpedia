-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_add
-- name    : Formalism.MainNotions.PlaneGram.ddiv_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:54.834882+00:00
-- url     : https://prove2.me/theorems/00073857-e52c-4a96-a9fe-b054b25b35d5
-- title:
--   Plane Gram: ddiv add
-- statement:
--   The Plane Gram construction uses the ddiv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L50-L51

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

theorem Formalism.MainNotions.PlaneGram.ddiv_add {σ : Type} (M : σ →₀ ℕ) (F G : MvPolynomial σ K) :
    ddiv M (F + G) = ddiv M F + ddiv M G := by sorry
