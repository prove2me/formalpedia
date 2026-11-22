-- Prove2me | Theorems.Thm_Formalism_LT_LTL_Near_pow
-- name    : Formalism.LT.LTL.Near.pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:08.058801+00:00
-- url     : https://prove2.me/theorems/11662174-8d0e-4b46-9d84-aa2fda1036fa
-- title:
--   Near: pow
-- statement:
--   The Near construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L34-L38

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
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

theorem Formalism.LT.LTL.Near.pow {k : ℕ} {A B : MvPowerSeries ι K} (h : Near k A B) (n : ℕ) :
    Near (k * n) (A ^ n) (B ^ n) := by sorry
