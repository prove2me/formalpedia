-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_Dn
-- name    : Formalism.CohomologicalDescent.LD.ld_sym_Dn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:21.571796+00:00
-- url     : https://prove2.me/theorems/fb450c85-dea5-4ff5-ae94-aea95b9a5d50
-- title:
--   LD: ld sym Dn
-- statement:
--   The LD construction uses the ld sym Dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L996-L1013
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L996-L1013

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

theorem Formalism.CohomologicalDescent.LD.ld_sym_Dn (q w i : ℕ) (hq : 0 < q) (hi : i ≤ w) :
    ((w.descFactorial i : ℕ) : ℤ) ∣ Dn 1 w i (fun _ : Fin q => 0) := by sorry
