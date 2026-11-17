-- Prove2me | Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
-- name    : APFPaper5.K1.turnTable_breaks_triangle
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:25:11.612987+00:00
-- url     : https://prove2.me/theorems/76c95021-b391-46ab-a299-faee4e826020
-- title:
--   turnTable breaks triangle
-- statement:
--   Result: turnTable breaks triangle. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem turnTable_breaks_triangle (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
--       turnTable x 0 0 < turnTable x 0 1 + turnTable x 0 2 - turnTable x 1 2
--   ```
--
--   Module context and limits: Nonnegative Boolean record tables obey the three-index bound. The supplied turnTable violates it for 0<x<1 but at x=1/2 is realized on real combinations of classes. Index 0 is the middle index, with neighbours 1 and 2. No physical turn or state realization is derived.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uW
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_record_tables_and_turns:127; pullbacks v39; source SHA-256 38d1144a58ac211ab5939a800f24a312157f10856ffeb5fdd016b73ec8af01e6']

import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Definitions.Def_APFPaper5_K1_MarkTable
import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
universe uI uW

/-! ### Every table of a record ledger obeys a three-distinction bound -/







/-! ### The table of a mark, its turn and its double turn -/

theorem APFPaper5.K1.turnTable_breaks_triangle (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    turnTable x 0 0 < turnTable x 0 1 + turnTable x 0 2 - turnTable x 1 2 := by sorry
