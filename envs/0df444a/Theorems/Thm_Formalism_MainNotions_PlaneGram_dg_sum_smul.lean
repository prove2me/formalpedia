-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_sum_smul
-- name    : Formalism.MainNotions.PlaneGram.dg_sum_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:06.83157+00:00
-- url     : https://prove2.me/theorems/ed2cde81-904c-4f72-b52c-19efc02dc145
-- title:
--   Plane Gram: dg sum smul
-- statement:
--   The Plane Gram construction uses the dg sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1146-L1150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1146-L1150

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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

theorem Formalism.MainNotions.PlaneGram.dg_sum_smul {σ ι : Type} (s : Finset ι) (lam : ι → K) (b : ι → (σ →₀ ℕ) → K)
    (F : MvPolynomial σ K) :
    dg (fun α => ∑ k ∈ s, lam k * b k α) F = ∑ k ∈ s, lam k • dg (b k) F := by sorry
