-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_eq_sum_of
-- name    : Formalism.MainNotions.PlaneGram.fock_eq_sum_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:06:42.178941+00:00
-- url     : https://prove2.me/theorems/30ab6ad7-db2f-4c74-bfb1-f58ac3a85df2
-- title:
--   Plane Gram: fock eq sum of
-- statement:
--   The Plane Gram construction uses the fock eq sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L78-L97

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

theorem Formalism.MainNotions.PlaneGram.fock_eq_sum_of (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : ∀ α, F.coeff α ≠ 0 → G.coeff α ≠ 0 → α ∈ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by sorry
