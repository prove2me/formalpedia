-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrc_applyWord_mem
-- name    : Formalism.CohomologicalDescent.LR.lrc_applyWord_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:47.844777+00:00
-- url     : https://prove2.me/theorems/70609d80-a60a-491f-909e-bece6859a062
-- title:
--   LR: lrc apply Word mem
-- statement:
--   The LR construction uses the lrc apply Word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L146-L152

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

theorem Formalism.CohomologicalDescent.LR.lrc_applyWord_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by sorry
