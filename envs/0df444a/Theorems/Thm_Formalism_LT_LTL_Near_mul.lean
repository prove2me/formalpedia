-- Prove2me | Theorems.Thm_Formalism_LT_LTL_Near_mul
-- name    : Formalism.LT.LTL.Near.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:43.779816+00:00
-- url     : https://prove2.me/theorems/b28844cb-6e9d-4c6d-8d35-a381ffa89d2e
-- title:
--   Near: mul
-- statement:
--   The Near construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L24-L29

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}

theorem Formalism.LT.LTL.Near.mul {k l : ℕ} {A B C D : MvPowerSeries ι K} (h1 : Near k A B) (h2 : Near l C D) :
    Near (k + l) (A * C) (B * D) := by sorry
