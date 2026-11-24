-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_eq_block_weight
-- name    : Formalism.CohomologicalDescent.LD.restriction_eq_block_weight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:30.438352+00:00
-- url     : https://prove2.me/theorems/0eaff874-cbb8-493e-966c-18286a7fc66e
-- title:
--   LD: restriction eq block weight
-- statement:
--   The LD construction uses the restriction eq block weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L292-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L292-L302

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

theorem Formalism.CohomologicalDescent.LD.restriction_eq_block_weight (n t : ℕ) (lam : ℕ → ℕ) (hc : ∀ a, n ≤ a → a < n + t → lam a = lam n) :
    res (n + t) lam = blockWtLast t n (lam n) (res n lam) := by sorry
