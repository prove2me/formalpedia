-- Prove2me | Theorems.Thm_CCRuleCW_curve_mem
-- name    : CCRuleCW.curve_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:17:28.364601+00:00
-- url     : https://prove2.me/theorems/658ea1bb-36b9-4f78-bae2-b62b4fcdf388
-- title:
--   CCRule CW: curve mem
-- statement:
--   The CCRule CW construction uses the curve mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L57-L64

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

theorem CCRuleCW.curve_mem (o : Bool × B.Mat k r) (g : B.Mat k r) (t : ℝ) (hX : B.inLie k r o.2)
    (hg : g ∈ B.GV k r) : curve o g t ∈ B.GV k r := by sorry
