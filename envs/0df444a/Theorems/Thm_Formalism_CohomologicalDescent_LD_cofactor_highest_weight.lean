-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_highest_weight
-- name    : Formalism.CohomologicalDescent.LD.cofactor_highest_weight
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:31.75575+00:00
-- url     : https://prove2.me/theorems/2c00f6cb-c0e5-4a38-973a-f724911fbf5a
-- title:
--   LD: cofactor highest weight
-- statement:
--   The LD construction uses the cofactor highest weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L902-L912
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L902-L912

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

theorem Formalism.CohomologicalDescent.LD.cofactor_highest_weight {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    genericDet ℤ r ^ (partialSumOfExponents ν 0) * cofMap r (hw ℤ le_rfl ν) = genericDet ℤ r ^ (∑ a, ν a) * ld3Q ν := by sorry
