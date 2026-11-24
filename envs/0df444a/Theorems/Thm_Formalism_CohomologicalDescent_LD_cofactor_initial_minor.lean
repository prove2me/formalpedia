-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_initial_minor
-- name    : Formalism.CohomologicalDescent.LD.cofactor_initial_minor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:12.296143+00:00
-- url     : https://prove2.me/theorems/64591b7c-63a2-4336-8268-7174bc1fb113
-- title:
--   LD: cofactor initial minor
-- statement:
--   The LD construction uses the cofactor initial minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L350-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L350-L384

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

theorem Formalism.CohomologicalDescent.LD.cofactor_initial_minor {r s t : ℕ} (h : s + t = r) (I : Fin s → Fin r) (hs : s ≤ r) :
    ∃ g ∈ dualWeyl ℤ r r (initW r t), genericDet ℤ r * cofMap r (initMinor ℤ I hs) = genericDet ℤ r ^ s * g := by sorry
