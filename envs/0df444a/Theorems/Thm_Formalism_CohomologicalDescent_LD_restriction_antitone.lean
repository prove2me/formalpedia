-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_restriction_antitone
-- name    : Formalism.CohomologicalDescent.LD.restriction_antitone
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:40.149299+00:00
-- url     : https://prove2.me/theorems/3c5afab4-853c-4014-a13a-e91bbfb181a8
-- title:
--   LD: restriction antitone
-- statement:
--   The LD construction uses the restriction antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L304-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L304-L305

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

theorem Formalism.CohomologicalDescent.LD.restriction_antitone (n : ℕ) (lam : ℕ → ℕ) (ha : ∀ a b, a ≤ b → b < n → lam b ≤ lam a) : Antitone (res n lam) := by sorry
