-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_map_generic_matrix
-- name    : Formalism.CohomologicalDescent.LD.cofactor_map_generic_matrix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:20.867027+00:00
-- url     : https://prove2.me/theorems/05cec822-9146-4d7f-8bdb-4f85bb04f279
-- title:
--   LD: cofactor map generic matrix
-- statement:
--   The LD construction uses the cofactor map generic matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L594-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L594-L599

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.cofactor_map_generic_matrix (r : ℕ) : (cofMap r).mapMatrix (genericMatrix' ℤ r) =
    ((genericMatrix' ℤ r).adjugate.transpose).submatrix Fin.revPerm Fin.revPerm := by sorry
