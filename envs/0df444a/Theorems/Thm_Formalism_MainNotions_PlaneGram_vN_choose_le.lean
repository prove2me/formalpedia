-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_choose_le
-- name    : Formalism.MainNotions.PlaneGram.vN_choose_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:08:17.603592+00:00
-- url     : https://prove2.me/theorems/fe1ffe81-eaad-42e7-88bd-fb5f1c54ad4d
-- title:
--   Plane Gram: v N choose le
-- statement:
--   The Plane Gram construction uses the v N choose le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L305-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L305-L309

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

theorem Formalism.MainNotions.PlaneGram.vN_choose_le (hD : DVRHyp v p) (n k : ℕ) : vN v (n.choose k) ≤ Nat.log p n := by sorry
