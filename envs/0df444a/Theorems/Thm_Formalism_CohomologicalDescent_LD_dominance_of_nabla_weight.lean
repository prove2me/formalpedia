-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_dominance_of_nabla_weight
-- name    : Formalism.CohomologicalDescent.LD.dominance_of_nabla_weight
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:14.980237+00:00
-- url     : https://prove2.me/theorems/8e2e5fb1-bf24-4bae-b5a3-c0b7728151b6
-- title:
--   LD: dominance of nabla weight
-- statement:
--   The LD construction uses the dominance of nabla weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L175-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L175-L186

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
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
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.dominance_of_nabla_weight (r : ℕ) (ν μ : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ nablaWt r ν μ) (hne : x ≠ 0) :
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, μ a) ≤ ∑ a : Fin r with a.val < k, ν a) ∧ ∑ a, μ a = ∑ a, ν a := by sorry
