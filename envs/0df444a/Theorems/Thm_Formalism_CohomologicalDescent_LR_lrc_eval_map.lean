-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_eval_map
-- name    : Formalism.CohomologicalDescent.LR.lrc_eval_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:07.973254+00:00
-- url     : https://prove2.me/theorems/b8d5e544-a220-4d6a-8e50-b9807e475f87
-- title:
--   LR: lrc eval map
-- statement:
--   The LR construction uses the lrc eval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L134-L144

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

theorem Formalism.CohomologicalDescent.LR.lrc_eval_map (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) P) = ((eval (idFrame ℤ r n) P : ℤ) : ℚ) := by sorry
