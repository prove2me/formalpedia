-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_neg_right
-- name    : Formalism.MainNotions.PlaneGram.fock_neg_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:58.424022+00:00
-- url     : https://prove2.me/theorems/a13e894b-be7f-4c7b-bb3a-ee7063a3763c
-- title:
--   Plane Gram: fock neg right
-- statement:
--   The Plane Gram construction uses the fock neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L137-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L137-L138

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

theorem Formalism.MainNotions.PlaneGram.fock_neg_right (F G : MvPolynomial σ K) : fock F (-G) = -fock F G := by sorry
