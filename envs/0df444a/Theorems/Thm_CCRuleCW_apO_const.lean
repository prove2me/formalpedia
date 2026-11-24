-- Prove2me | Theorems.Thm_CCRuleCW_apO_const
-- name    : CCRuleCW.apO_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:12.575711+00:00
-- url     : https://prove2.me/theorems/55d40463-d7cb-4586-8eb2-a80be23f9d8f
-- title:
--   CCRule CW: ap O const
-- statement:
--   The CCRule CW construction uses the ap O const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L71-L81

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem CCRuleCW.apO_const : ∀ (ops : List (Bool × B.Mat k r)) (c : ℂ),
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ apO ops (fun _ : B.Mat k r => c) = fun _ => c'
  := by sorry
