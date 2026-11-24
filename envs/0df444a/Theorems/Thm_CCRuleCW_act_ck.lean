-- Prove2me | Theorems.Thm_CCRuleCW_act_ck
-- name    : CCRuleCW.act_ck
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:17:46.280046+00:00
-- url     : https://prove2.me/theorems/7857d1ae-8fb9-46d9-9b30-e69185c5f901
-- title:
--   CCRule CW: act ck
-- statement:
--   The CCRule CW construction uses the act ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L120-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L120-L128

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

theorem CCRuleCW.act_ck (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (act o H) := by sorry
