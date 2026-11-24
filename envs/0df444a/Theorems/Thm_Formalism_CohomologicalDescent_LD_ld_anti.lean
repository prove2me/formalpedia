-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_anti
-- name    : Formalism.CohomologicalDescent.LD.ld_anti
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:41.923344+00:00
-- url     : https://prove2.me/theorems/57cfee78-c6f9-4df3-91cd-87a2fffca1da
-- title:
--   LD: ld anti
-- statement:
--   The LD construction uses the ld anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L202-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L202-L204

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

theorem Formalism.CohomologicalDescent.LD.ld_anti (w y : ℕ) (h : y ≤ w) : Antitone (wt2 w y) := by sorry
