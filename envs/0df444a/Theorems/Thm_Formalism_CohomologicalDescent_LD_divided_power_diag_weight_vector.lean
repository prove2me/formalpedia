-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_diag_weight_vector
-- name    : Formalism.CohomologicalDescent.LD.divided_power_diag_weight_vector
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:39.03171+00:00
-- url     : https://prove2.me/theorems/8ff695f4-a8a0-46f8-a578-1aa7b073d8c9
-- title:
--   LD: divided power diag weight vector
-- statement:
--   The LD construction uses the divided power diag weight vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L677-L687
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L677-L687

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

theorem Formalism.CohomologicalDescent.LD.divided_power_diag_weight_vector {r : ℕ} (a : Fin r) (k : ℕ) (μ : Fin r → ℕ) (y : MvPolynomial (Fin r × Fin r) ℤ)
    (hy : IsWeightedHomogeneous (rowW r r) y μ) : rowDiv ℤ a a k y = ((μ a).choose k : ℤ) • y := by sorry
