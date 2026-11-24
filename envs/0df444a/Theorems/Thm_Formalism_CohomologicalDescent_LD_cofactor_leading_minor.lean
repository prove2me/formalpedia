-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_leading_minor
-- name    : Formalism.CohomologicalDescent.LD.cofactor_leading_minor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:09.084678+00:00
-- url     : https://prove2.me/theorems/6e780102-b9c8-4b60-89e2-1922968f4ede
-- title:
--   LD: cofactor leading minor
-- statement:
--   The LD construction uses the cofactor leading minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L386-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L386-L403

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

theorem Formalism.CohomologicalDescent.LD.cofactor_leading_minor {r s t : ℕ} (h : s + t = r) (hs : s ≤ r) (ht : t ≤ r) :
    genericDet ℤ r * cofMap r (lpMinor ℤ s hs hs) = genericDet ℤ r ^ s * lpMinor ℤ t ht ht := by sorry
