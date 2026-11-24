-- Prove2me | Theorems.Thm_CCRuleCW_curve_hasDerivAt
-- name    : CCRuleCW.curve_hasDerivAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:13:40.116891+00:00
-- url     : https://prove2.me/theorems/1c937345-7210-4388-ad69-70a9f59da043
-- title:
--   CCRule CW: curve has Deriv At
-- statement:
--   The CCRule CW construction uses the curve has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L66-L83

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

theorem CCRuleCW.curve_hasDerivAt (o : Bool × B.Mat k r) (g : B.Mat k r) :
    HasDerivAt (curve o g) (dir o g) 0 := by sorry
