-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_dual_weight
-- name    : Formalism.CohomologicalDescent.LD.highest_weight_dual_weight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:36.754392+00:00
-- url     : https://prove2.me/theorems/0dc48e3e-0b5f-437d-a1c3-2446e307d322
-- title:
--   LD: highest weight dual weight
-- statement:
--   The LD construction uses the highest weight dual weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L924-L954
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L924-L954

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

theorem Formalism.CohomologicalDescent.LD.highest_weight_dual_weight {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ (M - partialSumOfExponents ν 0) * ld3Q ν := by sorry
