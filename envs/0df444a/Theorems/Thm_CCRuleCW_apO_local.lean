-- Prove2me | Theorems.Thm_CCRuleCW_apO_local
-- name    : CCRuleCW.apO_local
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:48:45.370047+00:00
-- url     : https://prove2.me/theorems/c47305c8-36e3-4a8a-9792-b17bfcd76475
-- title:
--   CCRule CW: ap O local
-- statement:
--   The CCRule CW construction uses the ap O local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L111-L115

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

theorem CCRuleCW.apO_local : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ f₁ f₂ : B.Mat k r → E,
    (∀ g ∈ B.GV k r, f₁ g = f₂ g) → ∀ g ∈ B.GV k r, apO ops f₁ g = apO ops f₂ g
  := by sorry
