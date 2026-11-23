-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_support_dg_subset
-- name    : Formalism.MainNotions.PlaneGram.support_dg_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:51.41384+00:00
-- url     : https://prove2.me/theorems/b04ee09b-9775-4260-8861-f9657ccbc1cf
-- title:
--   Plane Gram: support dg subset
-- statement:
--   The Plane Gram construction uses the support dg subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L174-L178

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
variable {σ : Type}

theorem Formalism.MainNotions.PlaneGram.support_dg_subset (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    (dg f F).support ⊆ F.support := by sorry
