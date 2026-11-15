-- Prove2me | Theorems.Thm_APFPaper5_K4_sums_of_books_differ_in_compositeOnly
-- name    : APFPaper5.K4.sums_of_books_differ_in_compositeOnly
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:56:17.662141+00:00
-- url     : https://prove2.me/theorems/6cc0f2fc-84ef-426f-be25-8035eb0453e8
-- title:
--   Sums of books differ in composite Only
-- statement:
--   The two explicit pairs of rate-free Joint states have summed compositeOnly readings minus two and plus two respectively. The compared sum of two books is not an adopted mixture/additivity law. This is not physical local tomography, field selection, or a derivation of rates.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_composite_only_reading.lean', 'sha256': 'fcf4a9f1946d52406cc95920e36573d87c42f381d92af590cb28cada7050a0b5', 'line': 121, 'declaration': 'APFPaper5.K4.sums_of_books_differ_in_compositeOnly'}]

import Definitions.Def_APFPaper5_K4_CompositeOnly
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.sums_of_books_differ_in_compositeOnly :
    linearRecord compositeOnly ⟨1, 0, 0, 0, 0, 0, -1, 0⟩ +
        linearRecord compositeOnly ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = -2 ∧
      linearRecord compositeOnly ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ +
        linearRecord compositeOnly ⟨0, 0, 1, 0, -1, 0, 0, 0⟩ = 2 := by sorry
