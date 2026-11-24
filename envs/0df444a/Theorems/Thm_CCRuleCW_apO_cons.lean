-- Prove2me | Theorems.Thm_CCRuleCW_apO_cons
-- name    : CCRuleCW.apO_cons
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:29:56.037928+00:00
-- url     : https://prove2.me/theorems/55be7533-7b4c-414c-9363-901ab95a826d
-- title:
--   CCRule CW: ap O cons
-- statement:
--   The CCRule CW construction uses the ap O cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L97-L98

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

theorem CCRuleCW.apO_cons (o : Bool × B.Mat k r) (os : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    apO (o :: os) f = apO os (act o f) := by sorry

attribute [defeq] CCRuleCW.apO_cons
