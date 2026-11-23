-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_binomialSeriesSubOne
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_binomialSeriesSubOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:10.671773+00:00
-- url     : https://prove2.me/theorems/4201ab9a-c025-40fc-9b98-2f9d5c5e7f3a
-- title:
--   Height Descent Minors: binomial Action binomial Series Sub One
-- statement:
--   The Height Descent Minors construction uses the binomial Action binomial Series Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L149-L152

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_binomialSeriesSubOne (c d : ℤ_[l]) : act l O c (br l O d) = br l O (d * c) := by sorry
