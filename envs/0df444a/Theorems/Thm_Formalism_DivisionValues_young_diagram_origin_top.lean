-- Prove2me | Theorems.Thm_Formalism_DivisionValues_young_diagram_origin_top
-- name    : Formalism.DivisionValues.young_diagram_origin_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:25.76049+00:00
-- url     : https://prove2.me/theorems/b7c91e32-bed3-418c-b6ad-4e0475cffca4
-- title:
--   Division Values: young diagram origin top
-- statement:
--   The Division Values construction uses the young diagram origin top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L228-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L228-L252

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

theorem Formalism.DivisionValues.young_diagram_origin_top : RowsOriginTop := by sorry
