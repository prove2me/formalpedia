-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_monomial_right
-- name    : Formalism.MainNotions.PlaneGram.fock_monomial_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:29.654156+00:00
-- url     : https://prove2.me/theorems/a233c0ab-9f02-4f52-baf3-a499a040ef45
-- title:
--   Plane Gram: fock monomial right
-- statement:
--   The Plane Gram construction uses the fock monomial right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L158-L162

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

theorem Formalism.MainNotions.PlaneGram.fock_monomial_right (F : MvPolynomial σ K) (α : σ →₀ ℕ) (c : K) :
    fock F (monomial α c) = F.coeff α * c * (fact α : K) := by sorry
