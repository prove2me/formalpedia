-- Prove2me | Theorems.Thm_Formalism_DivisionValues_young_diagram_origin_off
-- name    : Formalism.DivisionValues.young_diagram_origin_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:28.980179+00:00
-- url     : https://prove2.me/theorems/b4a959d9-c760-4c83-a61b-3b901b5a63ba
-- title:
--   Division Values: young diagram origin off
-- statement:
--   The Division Values construction uses the young diagram origin off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L212-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L212-L226

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues

theorem Formalism.DivisionValues.young_diagram_origin_off : RowsOriginOff := by sorry
