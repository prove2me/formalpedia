-- Prove2me | Theorems.Thm_Formalism_LT_LTL_inv_lin
-- name    : Formalism.LT.LTL.inv_lin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:28.128176+00:00
-- url     : https://prove2.me/theorems/25d7b857-0f25-4fca-aa4f-1348ee0566f9
-- title:
--   LTL: inv lin
-- statement:
--   The LTL construction uses the inv lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L510-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L510-L517

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

theorem Formalism.LT.LTL.inv_lin (_hS : LTSetting K p q π) (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    (ha : ∀ i, ‖a i‖ ≤ 1) : Inv e e' a 1 (lin a) := by sorry
