-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_Bd_sum
-- name    : Formalism.LT.CoeffP.Bd.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:59.332368+00:00
-- url     : https://prove2.me/theorems/f52eb4f5-26ae-4df6-99b3-7f534071f6b3
-- title:
--   Bd: sum
-- statement:
--   The Bd construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L129-L133

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
universe u v
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem Formalism.LT.CoeffP.Bd.sum {α : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset α} {F : α → MvPowerSeries ι K}
    (h : ∀ i ∈ s, Bd a (F i)) : Bd a (∑ i ∈ s, F i) := by sorry
