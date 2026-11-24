-- Prove2me | Theorems.Thm_CCRuleCW_sub_opsW
-- name    : CCRuleCW.sub_opsW
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:40.811291+00:00
-- url     : https://prove2.me/theorems/7b2220a2-9a4b-4f8c-81e5-c19428672707
-- title:
--   CCRule CW: sub ops W
-- statement:
--   The CCRule CW construction uses the sub ops W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L163-L170

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem CCRuleCW.sub_opsW (u v : List (B.Mat k r)) (l : List (Bool × B.Mat k r)) (h : l.Sublist (opsW u v)) :
    ∃ u' v', l = opsW u' v' ∧ (∀ X ∈ u', X ∈ u) ∧ (∀ X ∈ v', X ∈ v) := by sorry
