-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_mu_one
-- name    : Formalism.CohomologicalDescent.LD.ld_mu_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:41:09.648812+00:00
-- url     : https://prove2.me/theorems/c399927c-80c8-4d75-9439-87dc1f4c908e
-- title:
--   LD: ld mu one
-- statement:
--   The LD construction uses the ld mu one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L149-L157

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

theorem Formalism.CohomologicalDescent.LD.ld_mu_one (p w y i : ℕ) (hp : 1 ≤ p) (h : y + i ≤ w) (c : ℤ) :
    mu p w i (fun _ : Fin 1 => y) c = if (y : ℤ) ≤ c ∧ c < (y : ℤ) + (i : ℤ) then 1 else 0 := by sorry
