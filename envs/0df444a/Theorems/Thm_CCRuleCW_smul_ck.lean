-- Prove2me | Theorems.Thm_CCRuleCW_smul_ck
-- name    : CCRuleCW.smul_ck
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:19:00.178003+00:00
-- url     : https://prove2.me/theorems/4e9d671a-20b6-4610-b989-4f5f3c05dd84
-- title:
--   CCRule CW: smul ck
-- statement:
--   The CCRule CW construction uses the smul ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L148-L154

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

theorem CCRuleCW.smul_ck (Q : B.Mat k r → ℂ) (hQ : ContDiff ℝ ∞ Q) (H : B.Mat k r → E)
    (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H) : B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => Q g • H g) := by sorry
