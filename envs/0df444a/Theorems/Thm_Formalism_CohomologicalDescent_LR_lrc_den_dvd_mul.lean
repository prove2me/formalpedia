-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_den_dvd_mul
-- name    : Formalism.CohomologicalDescent.LR.lrc_den_dvd_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:54.223562+00:00
-- url     : https://prove2.me/theorems/3bbf244d-2602-46d2-ab9b-22039dd778d4
-- title:
--   LR: lrc den dvd mul
-- statement:
--   The LR construction uses the lrc den dvd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L200-L206

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

theorem Formalism.CohomologicalDescent.LR.lrc_den_dvd_mul (x : ℚ) (m : ℕ) (h : x.den ∣ m) : ∃ z : ℤ, (m : ℚ) * x = z := by sorry
