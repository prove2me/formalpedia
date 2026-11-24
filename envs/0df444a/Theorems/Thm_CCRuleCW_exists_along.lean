-- Prove2me | Theorems.Thm_CCRuleCW_exists_along
-- name    : CCRuleCW.exists_along
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:17:19.624965+00:00
-- url     : https://prove2.me/theorems/c55fed36-ecc4-4246-a4aa-8943d6f1f7d1
-- title:
--   CCRule CW: exists along
-- statement:
--   The CCRule CW construction uses the exists along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L114-L118

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

theorem CCRuleCW.exists_along (H : B.Mat k r → E) (hH : B.CkOn (⊤ : ℕ∞) (B.GV k r) H)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    ∃ v, HasDerivAt (fun t => H (curve o g t)) v 0 := by sorry
