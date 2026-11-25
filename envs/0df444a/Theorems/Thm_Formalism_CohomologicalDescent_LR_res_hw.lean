-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_res_hw
-- name    : Formalism.CohomologicalDescent.LR.res_hw
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:50.07884+00:00
-- url     : https://prove2.me/theorems/a79536fb-78d9-48cb-8ac4-2b5ea31c7b5f
-- title:
--   LR: res hw
-- statement:
--   The LR construction uses the res hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L275-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L275-L285

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
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

theorem Formalism.CohomologicalDescent.LR.res_hw (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    res ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2)) = hw ℚ le_rfl lam2 := by sorry
