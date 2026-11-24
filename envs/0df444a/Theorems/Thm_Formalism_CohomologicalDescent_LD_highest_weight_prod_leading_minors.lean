-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_prod_leading_minors
-- name    : Formalism.CohomologicalDescent.LD.highest_weight_prod_leading_minors
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:42.193496+00:00
-- url     : https://prove2.me/theorems/b0ec2c53-19a1-48de-8be6-695366f32d39
-- title:
--   LD: highest weight prod leading minors
-- statement:
--   The LD construction uses the highest weight prod leading minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L865-L872
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L865-L872

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

theorem Formalism.CohomologicalDescent.LD.highest_weight_prod_leading_minors {r : ℕ} (ν : Fin r → ℕ) :
    hw ℤ le_rfl ν = ∏ s ∈ Finset.range r, leadingMinorPolynomial r (s + 1) ^ (partialSumOfExponents ν s - partialSumOfExponents ν (s + 1)) := by sorry
