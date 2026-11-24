-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_dual_weyl_degree_bound
-- name    : Formalism.CohomologicalDescent.LD.dual_weyl_degree_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:05:46.357748+00:00
-- url     : https://prove2.me/theorems/75e816eb-1093-4209-ad2a-3483f9676d7f
-- title:
--   LD: dual weyl degree bound
-- statement:
--   The LD construction uses the dual weyl degree bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L105-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L105-L132

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

theorem Formalism.CohomologicalDescent.LD.dual_weyl_degree_bound {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (a : Fin r)
    (x : MvPolynomial (Fin r × Fin r) ℤ) (hx : x ∈ dualWeyl ℤ r r ν) :
    ∀ m ∈ x.support, rowDeg m a ≤ ν ⟨0, a.pos⟩ := by sorry
