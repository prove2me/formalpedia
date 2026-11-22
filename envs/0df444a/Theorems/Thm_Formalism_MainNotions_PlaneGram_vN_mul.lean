-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_mul
-- name    : Formalism.MainNotions.PlaneGram.vN_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:04.709979+00:00
-- url     : https://prove2.me/theorems/d99a9275-d826-471d-b8a0-594efbb0a3f4
-- title:
--   Plane Gram: v N mul
-- statement:
--   The Plane Gram construction uses the v N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L275-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L275-L280

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

theorem Formalism.MainNotions.PlaneGram.vN_mul (hD : DVRHyp v p) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    vN v (m * n) = vN v m + vN v n := by sorry
