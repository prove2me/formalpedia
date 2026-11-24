-- Prove2me | Theorems.Thm_CCRuleCW_term_bound
-- name    : CCRuleCW.term_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:40.565863+00:00
-- url     : https://prove2.me/theorems/8781d2b2-854a-4aeb-868a-b2409827af2c
-- title:
--   CCRule CW: term bound
-- statement:
--   The CCRule CW construction uses the term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L58-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChainRuleSmooth/LossBoundNonneg.lean#L58-L84

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

theorem CCRuleCW.term_bound {N A Bc m n a b C₁ C₂ : ℝ} {D : ℕ} (hN : 1 ≤ N) (hB : 0 ≤ Bc) (hmn : m ≤ n)
    (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ C₁ * N ^ D) (hb : N ^ (A - Bc * m) * b ≤ C₂) :
    N ^ (A - D - Bc * n) * (a * b) ≤ max C₁ 0 * max C₂ 0 := by sorry
