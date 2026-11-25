-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_mem_one_iff
-- name    : Formalism.CohomologicalDescent.LR.mem_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:28.918801+00:00
-- url     : https://prove2.me/theorems/2ee90778-0e87-4714-b0a3-52286a121607
-- title:
--   LR: mem one iff
-- statement:
--   The LR construction uses the mem one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L74-L80

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

theorem Formalism.CohomologicalDescent.LR.mem_one_iff (l : ℕ) (x : ℚ) : x ∈ (1 : Submodule (Zl l) ℚ) ↔ x ∈ Zl l := by sorry
