-- Prove2me | Theorems.Thm_Formalism_LT_FrobP_norm_le_of_mem_span
-- name    : Formalism.LT.FrobP.norm_le_of_mem_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:51:16.37879+00:00
-- url     : https://prove2.me/theorems/d4f4d7c7-d6f4-49be-8e7e-59cc93a08f2a
-- title:
--   Frob P: norm le of mem span
-- statement:
--   The Frob P construction uses the norm le of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L35-L44

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.FrobP.norm_le_of_mem_span {p : ℕ} (x : unitBall K)
    (hx : x ∈ Ideal.span {((p : ℕ) : unitBall K)}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by sorry
