-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_res_colHom
-- name    : Formalism.CohomologicalDescent.LR.res_colHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:50.579752+00:00
-- url     : https://prove2.me/theorems/4eae8aeb-8ee2-4871-ad2b-1eb8b018da50
-- title:
--   LR: res col Hom
-- statement:
--   The LR construction uses the res col Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L212-L215

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

theorem Formalism.CohomologicalDescent.LR.res_colHom (μ : Fin (p + q) → ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) R)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f μ) :
    IsWeightedHomogeneous (colW q q) (res R p q f) (fun b => μ (Fin.natAdd p b)) := by sorry
