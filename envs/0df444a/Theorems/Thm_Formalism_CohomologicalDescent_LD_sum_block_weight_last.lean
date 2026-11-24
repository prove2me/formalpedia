-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_block_weight_last
-- name    : Formalism.CohomologicalDescent.LD.sum_block_weight_last
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:52:20.12487+00:00
-- url     : https://prove2.me/theorems/f69ebe6b-9368-40b2-be57-a7f99dd0e355
-- title:
--   LD: sum block weight last
-- statement:
--   The LD construction uses the sum block weight last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L32-L36

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
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
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.sum_block_weight_last (p q w : ℕ) (lam2 : Fin q → ℕ) :
    ∑ a, blockWtLast p q w lam2 a = ∑ b, lam2 b + p * w := by sorry
