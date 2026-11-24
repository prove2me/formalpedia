-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_cast
-- name    : Formalism.CohomologicalDescent.LD.depth_two_cast
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:00.451059+00:00
-- url     : https://prove2.me/theorems/0ffd3659-6f0f-49d7-83e6-d0d63558fa64
-- title:
--   LD: depth two cast
-- statement:
--   The LD construction uses the depth two cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L197-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L197-L201

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

theorem Formalism.CohomologicalDescent.LD.depth_two_cast {r r' : ℕ} (h : r' = r) (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) :
    depth2 (fun a => ξ (Fin.cast h a)) (fun a => lam (Fin.cast h a)) (fun a => μ (Fin.cast h a)) =
      depth2 ξ lam μ := by sorry
