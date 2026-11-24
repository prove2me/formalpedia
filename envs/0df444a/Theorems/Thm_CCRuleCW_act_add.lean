-- Prove2me | Theorems.Thm_CCRuleCW_act_add
-- name    : CCRuleCW.act_add
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:54:44.611365+00:00
-- url     : https://prove2.me/theorems/06736337-4c1e-4260-8223-995873aa652f
-- title:
--   CCRule CW: act add
-- statement:
--   The CCRule CW construction uses the act add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L163-L170

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

theorem CCRuleCW.act_add (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (f₁ f₂ : B.Mat k r → E)
    (h₁ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁) (h₂ : B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    act o (fun x => f₁ x + f₂ x) g = act o f₁ g + act o f₂ g := by sorry
