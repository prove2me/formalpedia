-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_sq_dvd_one_add_pow_sub_linear
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.sq_dvd_one_add_pow_sub_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:38.754718+00:00
-- url     : https://prove2.me/theorems/49e3655d-1eb3-4b1c-8f48-49ee97a97f41
-- title:
--   Height Descent Minors: sq dvd one add pow sub linear
-- statement:
--   The Height Descent Minors construction uses the sq dvd one add pow sub linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1355-L1359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1355-L1359

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.sq_dvd_one_add_pow_sub_linear (R : Type) [CommRing R] (x v : R) (n : ℕ) :
    x ^ 2 ∣ (1 + x * v) ^ n - (1 + (n : R) * (x * v)) := by sorry
