-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_iff
-- name    : Formalism.MainNotions.PlaneGram.bge_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:15.86968+00:00
-- url     : https://prove2.me/theorems/57767c16-e35d-4599-992b-4c7b3e582e2e
-- title:
--   Plane Gram: bge iff
-- statement:
--   The Plane Gram construction uses the bge iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L198-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L198-L208

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

theorem Formalism.MainNotions.PlaneGram.bge_iff (a : ℝ) (F : MvPolynomial σ K) :
    bge v a F ↔ ((a : ℝ) : WithTop ℝ) ≤ vBB v F := by sorry
