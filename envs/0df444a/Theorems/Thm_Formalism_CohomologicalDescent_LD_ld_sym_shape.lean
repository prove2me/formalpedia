-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_shape
-- name    : Formalism.CohomologicalDescent.LD.ld_sym_shape
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:35.436658+00:00
-- url     : https://prove2.me/theorems/7050b3c4-57b3-482e-aea8-8a608797c56c
-- title:
--   LD: ld sym shape
-- statement:
--   The LD construction uses the ld sym shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L956-L979
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L956-L979

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

theorem Formalism.CohomologicalDescent.LD.ld_sym_shape (q w i : ℕ) (hi : i ≤ w) :
    (fun a : Fin q => if a.val = 0 then i else 0) ∈ shapes 1 w i (fun _ : Fin q => 0) ∨ q = 0 := by sorry
