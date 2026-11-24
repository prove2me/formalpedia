-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_card_filter_rev_lt_le
-- name    : Formalism.CohomologicalDescent.UnitNormBounds.card_filter_rev_lt_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:11.630143+00:00
-- url     : https://prove2.me/theorems/55bfca45-9fa7-4c0b-81ed-6f8a1027e333
-- title:
--   Unit Norm Bounds: card filter rev lt le
-- statement:
--   The Unit Norm Bounds construction uses the card filter rev lt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/UnitNormBounds.lean#L49-L60

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

theorem Formalism.CohomologicalDescent.UnitNormBounds.card_filter_rev_lt_le (k j : ℕ) (p : Fin (k + j) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧ p b).card ≤ k := by sorry
