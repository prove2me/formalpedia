-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.prime_sub_one_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:38.085485+00:00
-- url     : https://prove2.me/theorems/012dde35-3e1c-490b-8a0c-13774ba0061b
-- title:
--   Height Descent Minors: prime sub one pos
-- statement:
--   The Height Descent Minors construction uses the prime sub one pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L217-L219

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.prime_sub_one_pos : 0 < l - 1 := by sorry
