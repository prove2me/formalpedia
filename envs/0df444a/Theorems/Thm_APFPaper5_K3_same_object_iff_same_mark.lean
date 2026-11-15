-- Prove2me | Theorems.Thm_APFPaper5_K3_same_object_iff_same_mark
-- name    : APFPaper5.K3.same_object_iff_same_mark
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:43:05.774502+00:00
-- url     : https://prove2.me/theorems/0cd148dc-082d-49f3-9fb6-79933b9c0354
-- title:
--   Cost and mark classify the supplied continuation profile
-- statement:
--   Two Held2 states have equal plainAfterTurn profiles exactly when their totalCost values and markDirection triples agree. Same object means equality of this chosen profile only. No physical original-profile identification, uniqueness of all amplitude realizations, spatial dimension or Born interpretation is established.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717,3034-3076'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_marks_of_the_carrier.lean', 'sha256': '72c3402c8ce8841b045a22462ac40196ec9ee7f2b4fb09f734455d408c0f6b0d', 'line': 103, 'declaration': 'APFPaper5.K3.same_object_iff_same_mark'}]

import Definitions.Def_APFPaper5_K3_MarkOfHeld
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.same_object_iff_same_mark (h k : Held2) :
    plainAfterTurn h = plainAfterTurn k ↔
      totalCost h = totalCost k ∧ markDirection h = markDirection k := by sorry
