-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_step
-- name    : Formalism.CohomologicalDescent.LD.ld_sym_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:43.340527+00:00
-- url     : https://prove2.me/theorems/1fc4c1c9-8d71-4c87-a8f4-7c88717ce666
-- title:
--   LD: ld sym step
-- statement:
--   The LD construction uses the ld sym step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L849-L867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L849-L867

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

theorem Formalism.CohomologicalDescent.LD.ld_sym_step (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (a : Fin (1 + q))
    (ha : a ∉ S) (hz : ldZ q ∉ S) :
    rowDiv ℤ a (ldZ q) (μ a) (ldSv q w μ S) =
      ((w - ∑ b ∈ S, μ b).choose (μ a) : ℤ) • ldSv q w μ (insert a S) := by sorry
