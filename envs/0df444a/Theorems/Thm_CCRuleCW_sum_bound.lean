-- Prove2me | Theorems.Thm_CCRuleCW_sum_bound
-- name    : CCRuleCW.sum_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:13.466239+00:00
-- url     : https://prove2.me/theorems/6e6ccd18-a6f8-4bad-b95a-873be27c8321
-- title:
--   CCRule CW: sum bound
-- statement:
--   The CCRule CW construction uses the sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L44-L56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt

theorem CCRuleCW.sum_bound {α β : Type*} (l : List α) (S : Set β) (w : β → ℝ) (φ : α → β → ℝ)
    (h : ∀ p ∈ l, ∃ C, ∀ g ∈ S, φ p g ≤ C * w g) :
    ∃ C, ∀ g ∈ S, (l.map (fun p => φ p g)).sum ≤ C * w g := by sorry
