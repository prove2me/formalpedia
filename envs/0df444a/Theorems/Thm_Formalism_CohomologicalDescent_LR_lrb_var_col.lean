-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_var_col
-- name    : Formalism.CohomologicalDescent.LR.lrb_var_col
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:51:13.886649+00:00
-- url     : https://prove2.me/theorems/ac348894-3d78-476e-a281-869159175952
-- title:
--   LR: lrb var col
-- statement:
--   The LR construction uses the lrb var col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L169-L186

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
variable (R : Type*) [CommRing R] (p q : ℕ)

theorem Formalism.CohomologicalDescent.LR.lrb_var_col (v : Fin (p + q) × Fin (p + q)) :
    IsWeightedHomogeneous (colW q q) (resVar R p q v) (lrbPi p q (colW (p + q) (p + q) v)) := by sorry
