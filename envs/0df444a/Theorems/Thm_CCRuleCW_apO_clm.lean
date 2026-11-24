-- Prove2me | Theorems.Thm_CCRuleCW_apO_clm
-- name    : CCRuleCW.apO_clm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:42.330465+00:00
-- url     : https://prove2.me/theorems/40020266-4156-41b4-89cb-239f55e5a3c7
-- title:
--   CCRule CW: ap O clm
-- statement:
--   The CCRule CW construction uses the ap O clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/GoodMonoProd.lean#L102-L111

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

theorem CCRuleCW.apO_clm : ∀ (ops : List (Bool × B.Mat k r)) (ℓ : B.Mat k r →L[ℝ] ℂ),
    ∃ ℓ' : B.Mat k r →L[ℝ] ℂ, apO ops ⇑ℓ = ⇑ℓ'
  := by sorry
