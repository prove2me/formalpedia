-- Prove2me | Theorems.Thm_CCRuleCW_good_mul
-- name    : CCRuleCW.good_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:47.182821+00:00
-- url     : https://prove2.me/theorems/1bfbd9ab-2b74-48a8-a053-a757e4ab1e13
-- title:
--   CCRule CW: good mul
-- statement:
--   The CCRule CW construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L44-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L44-L69

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

theorem CCRuleCW.good_mul {a b : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good a Q₁) (h₂ : Good b Q₂) :
    Good (a + b) (fun g => Q₁ g * Q₂ g) := by sorry
