-- Prove2me | Theorems.Thm_CCRuleCW_mul_sum_map
-- name    : CCRuleCW.mul_sum_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:49.344082+00:00
-- url     : https://prove2.me/theorems/18c1e5a5-15c1-4755-bf2c-f4a206458d70
-- title:
--   CCRule CW: mul sum map
-- statement:
--   The CCRule CW construction uses the mul sum map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L38-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt

theorem CCRuleCW.mul_sum_map {α : Type*} (l : List α) (c : ℝ) (f : α → ℝ) :
    c * (l.map f).sum = (l.map (fun p => c * f p)).sum := by sorry
