-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos_alt
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.prime_sub_one_pos_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:48.519619+00:00
-- url     : https://prove2.me/theorems/dbe34291-f8ab-4c89-a1be-239c7f1a7660
-- title:
--   Height Descent Minors: prime sub one pos alt
-- statement:
--   The Height Descent Minors construction uses the prime sub one pos alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L998-L1000
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L998-L1000

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.prime_sub_one_pos_alt : 0 < l - 1 := by sorry
