-- Prove2me | Theorems.Thm_CCRuleCW_gN_pos
-- name    : CCRuleCW.gN_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:50.081805+00:00
-- url     : https://prove2.me/theorems/67248a35-9b0d-4b46-a46a-4ca22f69ca16
-- title:
--   CCRule CW: g N pos
-- statement:
--   The CCRule CW construction uses the g N pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L95-L96

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

theorem CCRuleCW.gN_pos {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) : 0 < B.gN g := by sorry
