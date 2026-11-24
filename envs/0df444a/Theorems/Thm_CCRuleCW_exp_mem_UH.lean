-- Prove2me | Theorems.Thm_CCRuleCW_exp_mem_UH
-- name    : CCRuleCW.exp_mem_UH
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:50:22.137282+00:00
-- url     : https://prove2.me/theorems/f4f20dff-1f61-4d65-83c0-01ebc0ffb009
-- title:
--   CCRule CW: exp mem UH
-- statement:
--   The CCRule CW construction uses the exp mem UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/ExpIntertwine.lean#L37-L44

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

theorem CCRuleCW.exp_mem_UH (H Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ Formalism.QuantumDeterminants.UH H := by sorry
