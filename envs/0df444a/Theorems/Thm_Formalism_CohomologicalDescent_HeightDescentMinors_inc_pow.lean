-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.inc_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:00.562001+00:00
-- url     : https://prove2.me/theorems/6d336878-d022-4052-b2c0-7ab568a8d082
-- title:
--   Height Descent Minors: inc pow
-- statement:
--   The Height Descent Minors construction uses the inc pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1016-L1017
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1016-L1017

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.inc_pow (f : O⟦X⟧) (n : ℕ) : inc l O (f ^ n) = inc l O f ^ n := by sorry
