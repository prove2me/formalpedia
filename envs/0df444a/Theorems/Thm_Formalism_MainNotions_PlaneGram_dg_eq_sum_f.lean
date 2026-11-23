-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_sum_f
-- name    : Formalism.MainNotions.PlaneGram.dg_eq_sum_f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:19.997086+00:00
-- url     : https://prove2.me/theorems/469bbbc2-120b-4848-b1d2-d2b3d6451fde
-- title:
--   Plane Gram: dg eq sum f
-- statement:
--   The Plane Gram construction uses the dg eq sum f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L168-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L168-L172

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

theorem Formalism.MainNotions.PlaneGram.dg_eq_sum_f (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg f F = ∑ α ∈ F.support, monomial α (f α * F.coeff α) := by sorry
