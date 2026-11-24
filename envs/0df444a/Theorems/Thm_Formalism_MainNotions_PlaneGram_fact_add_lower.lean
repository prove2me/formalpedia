-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_lower
-- name    : Formalism.MainNotions.PlaneGram.fact_add_lower
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:06:19.056377+00:00
-- url     : https://prove2.me/theorems/fc262edc-9ffb-4099-a335-5af980602f28
-- title:
--   Plane Gram: fact add lower
-- statement:
--   The Plane Gram construction uses the fact add lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L499-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L499-L530

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

theorem Formalism.MainNotions.PlaneGram.fact_add_lower (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α α' : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg (α + α') i = d i) :
    vN v (∏ i, (d i).factorial) - 2 * kapL p r d ≤ vN v (fact α) + vN v (fact α') := by sorry
