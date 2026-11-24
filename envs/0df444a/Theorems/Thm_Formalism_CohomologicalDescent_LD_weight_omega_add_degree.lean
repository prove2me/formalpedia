-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_omega_add_degree
-- name    : Formalism.CohomologicalDescent.LD.weight_omega_add_degree
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:58.01083+00:00
-- url     : https://prove2.me/theorems/7bf4edf9-443b-44b0-8fe2-1b9b39365a25
-- title:
--   LD: weight omega add degree
-- statement:
--   The LD construction uses the weight omega add degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L539-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L539-L558

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

theorem Formalism.CohomologicalDescent.LD.weight_omega_add_degree {r : ℕ} (d : Fin r × Fin r →₀ ℕ) (c : Fin r) :
    Finsupp.weight (diagonalEntryIndicator r) d c + rowDeg d (Fin.rev c) = ∑ a, rowDeg d a := by sorry
