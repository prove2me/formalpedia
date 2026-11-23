-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_height_descent_of_r3_r2
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.height_descent_of_r3_r2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:47.908299+00:00
-- url     : https://prove2.me/theorems/8246e55d-c27e-4c3d-94f5-cca700ae76e1
-- title:
--   Height Descent Minors: height descent of r3 r2
-- statement:
--   The Height Descent Minors construction uses the height descent of r3 r2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1788-L1831
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1788-L1831

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.height_descent_of_r3_r2 (h3 : UnitFactorQ) (hb : PowerSeriesFreeBasis) : HeightDescent := by sorry
