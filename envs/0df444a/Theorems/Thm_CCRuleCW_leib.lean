-- Prove2me | Theorems.Thm_CCRuleCW_leib
-- name    : CCRuleCW.leib
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:39.434716+00:00
-- url     : https://prove2.me/theorems/1580326a-5c16-4f63-8d6d-6cfac13173e5
-- title:
--   CCRule CW: leib
-- statement:
--   The CCRule CW construction uses the leib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L127-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L127-L139

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

theorem CCRuleCW.leib : ∀ (ops : List (Bool × B.Mat k r)), LieW ops → ∀ (Q : B.Mat k r → ℂ), ContDiff ℝ ∞ Q →
    ∀ (H : B.Mat k r → E), B.CkOn (⊤ : ℕ∞) (B.GV k r) H → ∀ g ∈ B.GV k r,
    apO ops (fun x => Q x • H x) g = ((splits ops).map (fun p => apO p.1 Q g • apO p.2 H g)).sum
  := by sorry
