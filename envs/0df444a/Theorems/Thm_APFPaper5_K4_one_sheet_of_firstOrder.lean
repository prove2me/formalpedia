-- Prove2me | Theorems.Thm_APFPaper5_K4_one_sheet_of_firstOrder
-- name    : APFPaper5.K4.one_sheet_of_firstOrder
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:05:37.317548+00:00
-- url     : https://prove2.me/theorems/937775af-d2f1-4499-9edc-8a571c3e122d
-- title:
--   One sheet of first Order
-- statement:
--   For a unit co-turn with nonzero sine, a Sheets state satisfying the displayed second-iterate span relation has either its synchronized component zero or its opposite component zero. Single-sheet selection consumes the joint cyclic-span law and additive closure. It is not derived from invisible local turns, a global orientation-network theorem, or physical K4.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2058-2090,2213-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_mirror_sheet.lean', 'sha256': '75029b115e6e401dbb2c211afb208c6dcdd0eda994cd083fc19457362ed1f192', 'line': 133, 'declaration': 'APFPaper5.K4.one_sheet_of_firstOrder'}]

import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.one_sheet_of_firstOrder (C S : ℝ) (hCS : C * C + S * S = 1) (hS : S ≠ 0) (p : Sheets)
    (hfo : ∃ α β : ℝ, coTurn C S (coTurn C S p) =
      sheetsAdd (sheetsSmul α p) (sheetsSmul β (coTurn C S p))) :
    p.sync = jointZero ∨ p.anti = jointZero := by sorry
