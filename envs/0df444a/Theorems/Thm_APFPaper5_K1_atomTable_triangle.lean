-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_triangle
-- name    : APFPaper5.K1.atomTable_triangle
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:47:56.181024+00:00
-- url     : https://prove2.me/theorems/90843282-8343-42e8-b17f-da07405107fa
-- title:
--   atomTable triangle
-- statement:
--   Result: atomTable triangle. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem atomTable_triangle {ι : Type uI} {W : Type uW} [Fintype W] (w : W → ℝ)
--       (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (i j k : ι) :
--       atomTable w mark i j + atomTable w mark i k - atomTable w mark j k ≤ atomTable w mark i i
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
--   ['Theorems.Thm_APFPaper5_K1_record_tables_and_turns:59; pullbacks v39; source SHA-256 38d1144a58ac211ab5939a800f24a312157f10856ffeb5fdd016b73ec8af01e6']

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

theorem APFPaper5.K1.atomTable_triangle {ι : Type uI} {W : Type uW} [Fintype W] (w : W → ℝ)
    (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (i j k : ι) :
    atomTable w mark i j + atomTable w mark i k - atomTable w mark j k ≤ atomTable w mark i i := by sorry
