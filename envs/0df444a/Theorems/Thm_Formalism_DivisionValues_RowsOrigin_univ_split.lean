-- Prove2me | Theorems.Thm_Formalism_DivisionValues_RowsOrigin_univ_split
-- name    : Formalism.DivisionValues.RowsOrigin.univ_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:21.2628+00:00
-- url     : https://prove2.me/theorems/ef89b8bb-6719-4413-bf51-0a59e614c427
-- title:
--   Rows Origin: univ split
-- statement:
--   The Rows Origin construction uses the univ split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramTopExact.lean#L105-L114

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
open Formalism.DivisionValues.RowsOrigin

theorem Formalism.DivisionValues.RowsOrigin.univ_split {n : ℕ} (g : Fin (n + 2) → ℕ) :
    (Finset.univ : Finset (Fin (n + 2))).val.map g =
      g 0 ::ₘ g (Fin.last (n + 1)) ::ₘ
        ((Finset.univ : Finset (Fin n)).val.map fun i => g i.castSucc.succ) := by sorry
