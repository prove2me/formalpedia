-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_inverse_holds
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.r2_inverse_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:30.927909+00:00
-- url     : https://prove2.me/theorems/17d74abc-6bf4-4d23-a5a9-cc425a4d7620
-- title:
--   Height Descent Minors: r2 inverse holds
-- statement:
--   The Height Descent Minors construction uses the r2 inverse holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L360-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L360-L380

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
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.r2_inverse_holds : DivisibilityInvariant := by sorry
