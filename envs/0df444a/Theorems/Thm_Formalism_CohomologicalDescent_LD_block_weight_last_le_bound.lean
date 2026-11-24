-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_block_weight_last_le_bound
-- name    : Formalism.CohomologicalDescent.LD.block_weight_last_le_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:21.641656+00:00
-- url     : https://prove2.me/theorems/e720a833-0483-4010-98d4-6b7f7350f252
-- title:
--   LD: block weight last le bound
-- statement:
--   The LD construction uses the block weight last le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L220-L227

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.block_weight_last_le_bound (p q w M : ℕ) (κ : Fin q → ℕ) (hκ : ∀ b, κ b ≤ M) (hw : w ≤ M) (a : Fin (q + p)) :
    blockWtLast p q w κ a ≤ M := by sorry
