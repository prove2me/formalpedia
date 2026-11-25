-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_zl_unit
-- name    : Formalism.CohomologicalDescent.LR.zl_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:24:09.758914+00:00
-- url     : https://prove2.me/theorems/18b81ec0-bfb1-4908-8499-cbd1a3fb7de5
-- title:
--   LR: zl unit
-- statement:
--   The LR construction uses the zl unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L64-L72

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LR.zl_unit {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : Zl l) := by sorry
