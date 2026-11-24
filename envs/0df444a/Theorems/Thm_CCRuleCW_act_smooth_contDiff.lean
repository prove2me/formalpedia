-- Prove2me | Theorems.Thm_CCRuleCW_act_smooth_contDiff
-- name    : CCRuleCW.act_smooth_contDiff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:16.472825+00:00
-- url     : https://prove2.me/theorems/b11434c5-5e13-42dc-a026-b77b326f8dcc
-- title:
--   CCRule CW: act smooth cont Diff
-- statement:
--   The CCRule CW construction uses the act smooth cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L140-L143

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem CCRuleCW.act_smooth_contDiff (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) (o : Bool × B.Mat k r) :
    ContDiff ℝ ∞ (act o Q) := by sorry
