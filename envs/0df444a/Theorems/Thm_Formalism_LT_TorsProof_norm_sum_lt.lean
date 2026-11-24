-- Prove2me | Theorems.Thm_Formalism_LT_TorsProof_norm_sum_lt
-- name    : Formalism.LT.TorsProof.norm_sum_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:16:44.522043+00:00
-- url     : https://prove2.me/theorems/21b1f66b-fc29-45b3-a2ec-cc1c91713d9e
-- title:
--   Tors Proof: norm sum lt
-- statement:
--   The Tors Proof construction uses the norm sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/TorsionNormIterProof.lean#L13-L18

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

theorem Formalism.LT.TorsProof.norm_sum_lt {s : Finset ℕ} {f : ℕ → K} {c : ℝ} (hc : 0 < c)
    (h : ∀ i ∈ s, ‖f i‖ < c) : ‖∑ i ∈ s, f i‖ < c := by sorry
