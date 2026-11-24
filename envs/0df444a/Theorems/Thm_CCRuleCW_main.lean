-- Prove2me | Theorems.Thm_CCRuleCW_main
-- name    : CCRuleCW.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:57:08.3513+00:00
-- url     : https://prove2.me/theorems/23dc7d30-5fc8-4fe0-a103-d4808bc233b2
-- title:
--   CCRule CW: main
-- statement:
--   The CCRule CW construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L179-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L179-L217

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

theorem CCRuleCW.main (A : ℝ) (D : ℕ) (Q : B.Mat k r → ℂ) (hQ : Good D Q) (F : B.Mat k r → E)
    (hF : C2.CCsc k r A F) : C2.CCsc k r (A - D) (fun g => Q g • F g) := by sorry
