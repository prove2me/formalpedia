-- Prove2me | Theorems.Thm_CCRuleCW_sup_le_gN
-- name    : CCRuleCW.sup_le_gN
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:33.99698+00:00
-- url     : https://prove2.me/theorems/596bc133-4093-4711-82b7-fe5bdeff9e92
-- title:
--   CCRule CW: sup le g N
-- statement:
--   The CCRule CW construction uses the sup le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L113-L114

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

theorem CCRuleCW.sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g := by sorry
