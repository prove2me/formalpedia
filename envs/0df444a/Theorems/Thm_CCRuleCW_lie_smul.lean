-- Prove2me | Theorems.Thm_CCRuleCW_lie_smul
-- name    : CCRuleCW.lie_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:37.42379+00:00
-- url     : https://prove2.me/theorems/7378921b-ff7a-47f9-835b-fd2f0109d20b
-- title:
--   CCRule CW: lie smul
-- statement:
--   The CCRule CW construction uses the lie smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L55-L58

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
variable {n : ℕ}

theorem CCRuleCW.lie_smul (H X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ * H + H * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * H + H * ((c : ℂ) • X) = 0 := by sorry
