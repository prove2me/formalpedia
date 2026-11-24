-- Prove2me | Theorems.Thm_Formalism_LT_TorsProof_term_le
-- name    : Formalism.LT.TorsProof.term_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:08.928517+00:00
-- url     : https://prove2.me/theorems/949384d8-b6bb-4e93-965e-5de0d23efa5f
-- title:
--   Tors Proof: term le
-- statement:
--   The Tors Proof construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L28-L38

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

theorem Formalism.LT.TorsProof.term_le (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ ≤ 1) {i : ℕ} (hiq : i ≠ q) :
    ‖e.coeff i * x ^ i‖ ≤ ‖π‖ * ‖x‖ := by sorry
