-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_mem_shapes_iff
-- name    : Formalism.CohomologicalDescent.LD.mem_shapes_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:52:47.695002+00:00
-- url     : https://prove2.me/theorems/e44b9272-b0f2-491a-9109-e3d92611efa0
-- title:
--   LD: mem shapes iff
-- statement:
--   The LD construction uses the mem shapes iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LastGradedImpliesOneBlock.lean#L57-L61

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

theorem Formalism.CohomologicalDescent.LD.mem_shapes_iff (p w i q : ℕ) (lam2 tau : Fin q → ℕ) :
    tau ∈ shapes p w i lam2 ↔ (∀ a, lam2 a ≤ tau a ∧ tau a ≤ lam2 a + i) ∧
      (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0 := by sorry
