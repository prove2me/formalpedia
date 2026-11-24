-- Prove2me | Theorems.Thm_CCRuleCW_norm_sum_map_le
-- name    : CCRuleCW.norm_sum_map_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:48:28.278393+00:00
-- url     : https://prove2.me/theorems/991a71b2-3d27-4fdf-aa03-93cd345361d3
-- title:
--   CCRule CW: norm sum map le
-- statement:
--   The CCRule CW construction uses the norm sum map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L30-L36

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

theorem CCRuleCW.norm_sum_map_le {α F : Type*} [SeminormedAddCommGroup F] (l : List α) (f : α → F) :
    ‖(l.map f).sum‖ ≤ (l.map (fun p => ‖f p‖)).sum := by sorry
