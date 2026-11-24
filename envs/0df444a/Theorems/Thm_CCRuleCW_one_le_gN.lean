-- Prove2me | Theorems.Thm_CCRuleCW_one_le_gN
-- name    : CCRuleCW.one_le_gN
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:57.867379+00:00
-- url     : https://prove2.me/theorems/e90b66db-978e-4e55-b536-007a35bb352c
-- title:
--   CCRule CW: one le g N
-- statement:
--   The CCRule CW construction uses the one le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L70-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L70-L93

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
open scoped Matrix.Norms.Frobenius

theorem CCRuleCW.one_le_gN {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by sorry
