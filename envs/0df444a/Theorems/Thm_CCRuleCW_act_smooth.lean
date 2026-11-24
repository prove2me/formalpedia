-- Prove2me | Theorems.Thm_CCRuleCW_act_smooth
-- name    : CCRuleCW.act_smooth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:54:54.654514+00:00
-- url     : https://prove2.me/theorems/367a5bbe-df57-40ab-b323-0b4e72068b5e
-- title:
--   CCRule CW: act smooth
-- statement:
--   The CCRule CW construction uses the act smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L130-L138

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

theorem CCRuleCW.act_smooth (Q : B.Mat k r → E) (hQ : ContDiff ℝ ∞ Q) (o : Bool × B.Mat k r) :
    act o Q = fun g => fderiv ℝ Q g (dir o g) := by sorry
