-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_intQ_apply
-- name    : Formalism.CohomologicalDescent.LR.lrc_intQ_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:58.330919+00:00
-- url     : https://prove2.me/theorems/0875693f-566b-40a9-ac78-f9183646abcb
-- title:
--   LR: lrc int Q apply
-- statement:
--   The LR construction uses the lrc int Q apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L131-L132

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

theorem Formalism.CohomologicalDescent.LR.lrc_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := by sorry
