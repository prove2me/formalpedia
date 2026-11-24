-- Prove2me | Theorems.Thm_CCRuleCW_along
-- name    : CCRuleCW.along
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:16:58.343806+00:00
-- url     : https://prove2.me/theorems/23864c85-d2ee-4224-9873-3a40de1b0231
-- title:
--   CCRule CW: along
-- statement:
--   The CCRule CW construction uses the along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/Curves.lean#L98-L112

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

theorem CCRuleCW.along (H : B.Mat k r → E) {U : Set (B.Mat k r)} {f' : B.Mat k r → E} (hU : IsOpen U)
    (hf' : ContDiffOn ℝ ∞ f' U) (hagree : ∀ g ∈ U, g ∈ B.GV k r → H g = f' g)
    (o : Bool × B.Mat k r) (hX : B.inLie k r o.2) (g : B.Mat k r) (hgU : g ∈ U) (hg : g ∈ B.GV k r) :
    HasDerivAt (fun t => H (curve o g t)) (fderiv ℝ f' g (dir o g)) 0 := by sorry
