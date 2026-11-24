-- Prove2me | Theorems.Thm_CCRuleCW_exp_intertwine
-- name    : CCRuleCW.exp_intertwine
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:19.924007+00:00
-- url     : https://prove2.me/theorems/4bb1ba53-8c8b-4a2b-98cb-9e19feacc760
-- title:
--   CCRule CW: exp intertwine
-- statement:
--   The CCRule CW construction uses the exp intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L17-L34

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
set_option backward.isDefEq.respectTransparency false

theorem CCRuleCW.exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by sorry
