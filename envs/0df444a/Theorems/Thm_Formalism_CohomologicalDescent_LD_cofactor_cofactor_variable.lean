-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_cofactor_variable
-- name    : Formalism.CohomologicalDescent.LD.cofactor_cofactor_variable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:35.230443+00:00
-- url     : https://prove2.me/theorems/b3200bb7-f572-40f9-9a43-16996e4b5096
-- title:
--   LD: cofactor cofactor variable
-- statement:
--   The LD construction uses the cofactor cofactor variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L612-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L612-L624

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

theorem Formalism.CohomologicalDescent.LD.cofactor_cofactor_variable (r : ℕ) (v : Fin r × Fin r) :
    genericDet ℤ r * cofMap r (cofMap r (X v)) = genericDet ℤ r ^ (r - 1) * X v := by sorry
