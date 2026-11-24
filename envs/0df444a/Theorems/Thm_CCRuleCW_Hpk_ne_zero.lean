-- Prove2me | Theorems.Thm_CCRuleCW_Hpk_ne_zero
-- name    : CCRuleCW.Hpk_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:24.537826+00:00
-- url     : https://prove2.me/theorems/d3f7114c-6a23-4dbf-92c5-0150d83336c1
-- title:
--   CCRule CW: Hpk ne zero
-- statement:
--   The CCRule CW construction uses the Hpk ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L62-L67

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

theorem CCRuleCW.Hpk_ne_zero (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r ≠ 0 := by sorry
