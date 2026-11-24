-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_lt_q_eq_sum_cast_add
-- name    : Formalism.CohomologicalDescent.LD.sum_lt_q_eq_sum_cast_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:23.133891+00:00
-- url     : https://prove2.me/theorems/9e6f7cf2-1977-4fe4-a651-7d20a6d03b2a
-- title:
--   LD: sum lt q eq sum cast add
-- statement:
--   The LD construction uses the sum lt q eq sum cast add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L217-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L217-L220

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

theorem Formalism.CohomologicalDescent.LD.sum_lt_q_eq_sum_cast_add (p q : ℕ) (f : Fin (q + p) → ℕ) :
    (∑ a : Fin (q + p) with a.val < q, f a) = ∑ b : Fin q, f (Fin.castAdd p b) := by sorry
