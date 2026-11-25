-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_highest_weight_dual_cofactor
-- name    : Formalism.CohomologicalDescent.LD.highest_weight_dual_cofactor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:43.527806+00:00
-- url     : https://prove2.me/theorems/29a56a18-e2be-4281-8d3f-ea7c7915a61a
-- title:
--   LD: highest weight dual cofactor
-- statement:
--   The LD construction uses the highest weight dual cofactor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L956-L963
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L956-L963

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

theorem Formalism.CohomologicalDescent.LD.highest_weight_dual_cofactor {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (hM : ∀ a, ν a ≤ M) :
    genericDet ℤ r ^ (∑ a, ν a) * hw ℤ le_rfl (dualWt M ν) = genericDet ℤ r ^ M * cofMap r (hw ℤ le_rfl ν) := by sorry
