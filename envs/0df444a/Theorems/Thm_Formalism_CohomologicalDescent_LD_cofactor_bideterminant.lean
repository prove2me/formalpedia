-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_bideterminant
-- name    : Formalism.CohomologicalDescent.LD.cofactor_bideterminant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:21.92249+00:00
-- url     : https://prove2.me/theorems/32707f5a-9464-4b74-87d8-b0a8ed7b9ef7
-- title:
--   LD: cofactor bideterminant
-- statement:
--   The LD construction uses the cofactor bideterminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L405-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L405-L413

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

theorem Formalism.CohomologicalDescent.LD.cofactor_bideterminant {r K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∃ g ∈ dualWeyl ℤ r r (∑ k, initW r (r - sz k)),
      genericDet ℤ r ^ K * cofMap r (bideterminant ℤ sz hsz I) = genericDet ℤ r ^ (∑ k, sz k) * g := by sorry
