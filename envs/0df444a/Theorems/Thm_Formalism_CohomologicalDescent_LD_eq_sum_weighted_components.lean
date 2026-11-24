-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_eq_sum_weighted_components
-- name    : Formalism.CohomologicalDescent.LD.eq_sum_weighted_components
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:05:13.25877+00:00
-- url     : https://prove2.me/theorems/9fa14db1-b96e-4acd-b9bf-4e1210b765d8
-- title:
--   LD: eq sum weighted components
-- statement:
--   The LD construction uses the eq sum weighted components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L725-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L725-L727

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

theorem Formalism.CohomologicalDescent.LD.eq_sum_weighted_components {r : ℕ} (x : MvPolynomial (Fin r × Fin r) ℤ) :
    ∃ S : Finset (Fin r → ℕ), x = ∑ μ ∈ S, weightedHomogeneousComponent (rowW r r) μ x := by sorry
