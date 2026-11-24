-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sum_right
-- name    : Formalism.MainNotions.PlaneGram.fock_sum_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:15.18629+00:00
-- url     : https://prove2.me/theorems/c5ec9e23-4009-42bd-b370-154fb2b945e6
-- title:
--   Plane Gram: fock sum right
-- statement:
--   The Plane Gram construction uses the fock sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L153-L156

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

theorem Formalism.MainNotions.PlaneGram.fock_sum_right {ι : Type} (s : Finset ι) (F : MvPolynomial σ K) (f : ι → MvPolynomial σ K) :
    fock F (∑ i ∈ s, f i) = ∑ i ∈ s, fock F (f i) := by sorry
