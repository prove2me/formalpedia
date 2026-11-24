-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_of_dual_weights
-- name    : Formalism.CohomologicalDescent.LD.depth_two_of_dual_weights
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:49.744866+00:00
-- url     : https://prove2.me/theorems/d3e99e0c-7a29-40a6-82a2-7654154347bc
-- title:
--   LD: depth two of dual weights
-- statement:
--   The LD construction uses the depth two of dual weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L203-L209

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

theorem Formalism.CohomologicalDescent.LD.depth_two_of_dual_weights (p q M : ℕ) (ξ : Fin (q + p) → ℤ) (lam μ : Fin (q + p) → ℕ)
    (hl : ∀ a, lam a ≤ M) (hm : ∀ a, μ a ≤ M) :
    depth2 (fun a : Fin (p + q) => -ξ (Fin.rev (Fin.cast (Nat.add_comm p q) a)))
      (fun a => dualWt M lam (Fin.cast (Nat.add_comm p q) a))
      (fun a => dualWt M μ (Fin.cast (Nat.add_comm p q) a)) = depth2 ξ lam μ := by sorry
