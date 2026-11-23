-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_rootsDescent_of_roots_and_fourth_relation
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.rootsDescent_of_roots_and_fourth_relation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:44.327077+00:00
-- url     : https://prove2.me/theorems/1ca07061-4a71-4d0e-94ea-5dcb702fe149
-- title:
--   Height Descent Minors: roots Descent of roots and fourth relation
-- statement:
--   The Height Descent Minors construction uses the roots Descent of roots and fourth relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1768-L1782
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1768-L1782

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.rootsDescent_of_roots_and_fourth_relation (hr : QRoots) (h4 : R4) : RootsDescent := by sorry
