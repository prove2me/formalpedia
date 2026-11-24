-- Prove2me | Theorems.Thm_CCRuleCW_mem_splits
-- name    : CCRuleCW.mem_splits
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:48:33.440889+00:00
-- url     : https://prove2.me/theorems/fa077afd-fb91-4c7c-af98-ead2fa9b97a4
-- title:
--   CCRule CW: mem splits
-- statement:
--   The CCRule CW construction uses the mem splits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L16-L28

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

theorem CCRuleCW.mem_splits {α : Type*} : ∀ (l : List α) (p : List α × List α), p ∈ splits l →
    p.1.Sublist l ∧ p.2.Sublist l
  := by sorry
