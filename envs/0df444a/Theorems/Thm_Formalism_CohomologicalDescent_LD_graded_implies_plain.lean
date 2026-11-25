-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_graded_implies_plain
-- name    : Formalism.CohomologicalDescent.LD.graded_implies_plain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:20.354213+00:00
-- url     : https://prove2.me/theorems/b5c2b218-a3a6-44dc-a4c5-7617e8d4403b
-- title:
--   LD: graded implies plain
-- statement:
--   The LD construction uses the graded implies plain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L1064-L1064
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L1064-L1064

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

theorem Formalism.CohomologicalDescent.LD.graded_implies_plain : GradedImpliesPlain := by sorry
