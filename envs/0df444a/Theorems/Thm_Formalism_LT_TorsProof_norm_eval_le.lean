-- Prove2me | Theorems.Thm_Formalism_LT_TorsProof_norm_eval_le
-- name    : Formalism.LT.TorsProof.norm_eval_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:46.674941+00:00
-- url     : https://prove2.me/theorems/04393ebe-8ef8-4835-8628-3519ce7c6908
-- title:
--   Tors Proof: norm eval le
-- statement:
--   The Tors Proof construction uses the norm eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L45-L55

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {π : K} {q : ℕ} {e : Polynomial K}

theorem Formalism.LT.TorsProof.norm_eval_le (hq : 2 ≤ q) (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ < 1)
    (hsmall : ‖x‖ ^ (q - 1) ≤ ‖π‖) : ‖e.eval x‖ ≤ ‖π‖ * ‖x‖ := by sorry
