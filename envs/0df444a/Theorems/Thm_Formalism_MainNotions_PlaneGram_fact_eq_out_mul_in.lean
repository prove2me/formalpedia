-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_out_mul_in
-- name    : Formalism.MainNotions.PlaneGram.fact_eq_out_mul_in
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:06:43.237351+00:00
-- url     : https://prove2.me/theorems/c6d8db5f-f6b8-4640-8253-a5bc3bf9465d
-- title:
--   Plane Gram: fact eq out mul in
-- statement:
--   The Plane Gram construction uses the fact eq out mul in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L339-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L339-L342

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

theorem Formalism.MainNotions.PlaneGram.fact_eq_out_mul_in {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α : L × Fin r →₀ ℕ) : fact α = fact (eOut out α) * fact (eIn out α) := by sorry
