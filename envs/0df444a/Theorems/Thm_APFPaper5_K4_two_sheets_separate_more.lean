-- Prove2me | Theorems.Thm_APFPaper5_K4_two_sheets_separate_more
-- name    : APFPaper5.K4.two_sheets_separate_more
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:07:14.733211+00:00
-- url     : https://prove2.me/theorems/b0ce6a39-7b6b-4374-9f60-3b0bed8f5e2f
-- title:
--   Two sheets separate more
-- statement:
--   There exist two Sheets states with equal synchronized components but different values of a specified sheetwise quadratic record. FirstOrder means second iterate in a two-vector span, not equivalence to faithful differentiable first jets or a derivation from economy. The reverse implication and exact two-dimensional physical minimality are not certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2058-2090'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_firstOrder_economy.lean', 'sha256': '18c13508d187b79c5c4e62912fc2007b8a37738e601401e754d9db7bbe19fd59', 'line': 94, 'declaration': 'APFPaper5.K4.two_sheets_separate_more'}]

import Definitions.Def_APFPaper5_K3_FirstOrder
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K4_TwoSheets
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

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1








namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.two_sheets_separate_more :
    ∃ p q : Sheets, p.sync = q.sync ∧
      ∃ w w' : RecordWeights, sheetsReading w w' p ≠ sheetsReading w w' q := by sorry
