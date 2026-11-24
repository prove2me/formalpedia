-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sub_left
-- name    : Formalism.MainNotions.PlaneGram.fock_sub_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:07:07.28404+00:00
-- url     : https://prove2.me/theorems/d259bfb3-d42c-418c-9517-12666a963033
-- title:
--   Plane Gram: fock sub left
-- statement:
--   The Plane Gram construction uses the fock sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L140-L141

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

theorem Formalism.MainNotions.PlaneGram.fock_sub_left (F F' G : MvPolynomial σ K) : fock (F - F') G = fock F G - fock F' G := by sorry
