-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_eq_sum
-- name    : Formalism.MainNotions.PlaneGram.fock_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:47.194845+00:00
-- url     : https://prove2.me/theorems/9c6cea06-3044-4215-b9ad-28783db2315f
-- title:
--   Plane Gram: fock eq sum
-- statement:
--   The Plane Gram construction uses the fock eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L99-L106

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

theorem Formalism.MainNotions.PlaneGram.fock_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ))
    (h : F.support ⊆ s ∨ G.support ⊆ s) :
    fock F G = ∑ α ∈ s, F.coeff α * G.coeff α * (fact α : K) := by sorry
