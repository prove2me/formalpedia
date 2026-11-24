-- Prove2me | Theorems.Thm_CCRuleCW_act_eq
-- name    : CCRuleCW.act_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:12:14.408824+00:00
-- url     : https://prove2.me/theorems/b256959e-dd02-4365-bacc-464f3dbc7b62
-- title:
--   CCRule CW: act eq
-- statement:
--   The CCRule CW construction uses the act eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L48-L51

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

theorem CCRuleCW.act_eq (o : Bool × B.Mat k r) (f : B.Mat k r → E) (g : B.Mat k r) :
    act o f g = deriv (fun t : ℝ => f (curve o g t)) 0 := by sorry
