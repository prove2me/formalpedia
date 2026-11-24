-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vle_vN
-- name    : Formalism.MainNotions.PlaneGram.vle_vN
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:31.786823+00:00
-- url     : https://prove2.me/theorems/6539b384-7d9c-4a7b-9add-ee783037c31c
-- title:
--   Plane Gram: vle v N
-- statement:
--   The Plane Gram construction uses the vle v N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L267-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L267-L269

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]

theorem Formalism.MainNotions.PlaneGram.vle_vN (hD : DVRHyp v p) {n : ℕ} (hn : n ≠ 0) : vle v (vN v n) (n : K) := by sorry
