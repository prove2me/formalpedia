-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_eq_zero_iff_norm_lt_one
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_eq_zero_iff_norm_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:37.039441+00:00
-- url     : https://prove2.me/theorems/b246e23f-261b-4700-9fe7-099354e00cdd
-- title:
--   Height Descent Minors: to ZMod eq zero iff norm lt one
-- statement:
--   The Height Descent Minors construction uses the to ZMod eq zero iff norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L224-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L224-L225

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
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_eq_zero_iff_norm_lt_one (y : ℤ_[l]) : PadicInt.toZMod y = 0 ↔ ‖y‖ < 1 := by sorry
