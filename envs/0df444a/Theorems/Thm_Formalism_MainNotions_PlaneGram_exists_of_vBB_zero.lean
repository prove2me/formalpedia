-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_exists_of_vBB_zero
-- name    : Formalism.MainNotions.PlaneGram.exists_of_vBB_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:20.904803+00:00
-- url     : https://prove2.me/theorems/9b4167bb-7242-4cd2-b19c-14d380eae46c
-- title:
--   Plane Gram: exists of v BB zero
-- statement:
--   The Plane Gram construction uses the exists of v BB zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L226-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L226-L249

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

theorem Formalism.MainNotions.PlaneGram.exists_of_vBB_zero (F : MvPolynomial σ K) (h : vBB v F = 0) :
    (∃ α ∈ F.support, vge v (-(vN v (fact α)) / 2) (F.coeff α) ∧
      vle v (-(vN v (fact α)) / 2) (F.coeff α)) ∧ bge v 0 F := by sorry
