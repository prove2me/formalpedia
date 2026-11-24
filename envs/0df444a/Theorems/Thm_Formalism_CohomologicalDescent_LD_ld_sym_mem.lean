-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_mem
-- name    : Formalism.CohomologicalDescent.LD.ld_sym_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:00.607171+00:00
-- url     : https://prove2.me/theorems/d7743685-047b-41c3-a97c-d43689310991
-- title:
--   LD: ld sym mem
-- statement:
--   The LD construction uses the ld sym mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L869-L897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L869-L897

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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

theorem Formalism.CohomologicalDescent.LD.ld_sym_mem (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (hz : ldZ q ∉ S)
    (hS : ∑ a ∈ S, μ a ≤ w) :
    ∃ c : ℕ, c ∣ w.descFactorial (∑ a ∈ S, μ a) ∧
      (c : ℤ) • ldSv q w μ S ∈ weyl ℤ (1 + q) (1 + q) le_rfl (blockWt 1 q w fun _ => 0) := by sorry
