-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_mem_dual_weyl
-- name    : Formalism.CohomologicalDescent.LD.rank_two_vector_mem_dual_weyl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:27.313212+00:00
-- url     : https://prove2.me/theorems/391c7a77-13e2-45ca-afdf-1aac92106185
-- title:
--   LD: rank two vector mem dual weyl
-- statement:
--   The LD construction uses the rank two vector mem dual weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L347-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L347-L356

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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

theorem Formalism.CohomologicalDescent.LD.rank_two_vector_mem_dual_weyl (w y i : ℕ) (h : y + i ≤ w) : vec2 w y i ∈ dualWeyl ℤ 2 2 (wt2 w y) := by sorry
