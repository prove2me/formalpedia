-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_one_add_pow_eq_linear_add_sq_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.one_add_pow_eq_linear_add_sq_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:05.782839+00:00
-- url     : https://prove2.me/theorems/8d157dba-d963-4434-a495-b7b7599a512b
-- title:
--   Height Descent Minors: one add pow eq linear add sq mul
-- statement:
--   The Height Descent Minors construction uses the one add pow eq linear add sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1142-L1151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1142-L1151

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.HeightDescentMinors.one_add_pow_eq_linear_add_sq_mul {R : Type} [CommRing R] (x : R) (n : ℕ) :
    ∃ e, (1 + x) ^ n = 1 + (n : R) * x + x ^ 2 * e := by sorry
