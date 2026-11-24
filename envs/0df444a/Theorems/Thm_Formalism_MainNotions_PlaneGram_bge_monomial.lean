-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_monomial
-- name    : Formalism.MainNotions.PlaneGram.bge_monomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:41.599834+00:00
-- url     : https://prove2.me/theorems/c3609968-0398-4a95-af20-f19dd7343694
-- title:
--   Plane Gram: bge monomial
-- statement:
--   The Plane Gram construction uses the bge monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L213-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L213-L219

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
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
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

theorem Formalism.MainNotions.PlaneGram.bge_monomial {a : ℝ} (α : σ →₀ ℕ) {c : K} (hc : vge v a c) :
    bge v (a + vN v (fact α) / 2) (monomial α c) := by sorry
