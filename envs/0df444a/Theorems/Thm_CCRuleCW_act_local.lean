-- Prove2me | Theorems.Thm_CCRuleCW_act_local
-- name    : CCRuleCW.act_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:56:00.21847+00:00
-- url     : https://prove2.me/theorems/6106679a-ff9f-45f0-88ae-69f159131d88
-- title:
--   CCRule CW: act local
-- statement:
--   The CCRule CW construction uses the act local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L156-L161

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

theorem CCRuleCW.act_local (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (f₁ f₂ : B.Mat k r → E)
    (h : ∀ g ∈ B.GV k r, f₁ g = f₂ g) (g : B.Mat k r) (hg : g ∈ B.GV k r) : act o f₁ g = act o f₂ g := by sorry
