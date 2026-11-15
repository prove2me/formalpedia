-- Prove2me | Theorems.Thm_APFPaper5_K3_number_between
-- name    : APFPaper5.K3.number_between
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:36:13.719936+00:00
-- url     : https://prove2.me/theorems/4cae3847-2cf5-42d2-a5e2-668b475e8137
-- title:
--   Number between
-- statement:
--   For two Held2 states, twice their defined overlap equals the product of total costs plus the dot product of their markDirection triples. Same object means equality of this chosen profile only. No physical original-profile identification, uniqueness of all amplitude realizations, spatial dimension or Born interpretation is established.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717,3034-3076'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_marks_of_the_carrier.lean', 'sha256': '72c3402c8ce8841b045a22462ac40196ec9ee7f2b4fb09f734455d408c0f6b0d', 'line': 55, 'declaration': 'APFPaper5.K3.number_between'}]

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

theorem APFPaper5.K3.number_between (h k : Held2) :
    2 * overlap h k = totalCost h * totalCost k + dot3 (markDirection h) (markDirection k) := by sorry
