-- Prove2me | Theorems.Thm_CCRuleCW_apO_add
-- name    : CCRuleCW.apO_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:30:11.307892+00:00
-- url     : https://prove2.me/theorems/59d45fb2-152e-4f94-a3f7-a8d8d5df16d8
-- title:
--   CCRule CW: ap O add
-- statement:
--   The CCRule CW construction uses the ap O add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L117-L125

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

theorem CCRuleCW.apO_add : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ f₁ f₂ : B.Mat k r → E,
    B.CkOn (⊤ : ℕ∞) (B.GV k r) f₁ → B.CkOn (⊤ : ℕ∞) (B.GV k r) f₂ →
    ∀ g ∈ B.GV k r, apO ops (fun x => f₁ x + f₂ x) g = apO ops f₁ g + apO ops f₂ g
  := by sorry
