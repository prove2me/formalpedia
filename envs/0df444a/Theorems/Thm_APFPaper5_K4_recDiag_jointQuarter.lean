-- Prove2me | Theorems.Thm_APFPaper5_K4_recDiag_jointQuarter
-- name    : APFPaper5.K4.recDiag_jointQuarter
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:05:35.373614+00:00
-- url     : https://prove2.me/theorems/24463f88-2c02-4cbf-85ab-c5d7cd7ff0d8
-- title:
--   Rec Diag joint Quarter
-- statement:
--   Supporting result: rec Diag joint Quarter. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. For a real-linear Joint endomap, quarter invariance of recDiag after the map yields a linearRecord representation. Thus the map-level extension predicate implies the record-level one and excludes rateFlip. The linearity and quarter-invariance premises remain structural assumptions about the supplied joint map; no general physical-process linearity theorem is claimed.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044,2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_record_book_linear.lean', 'sha256': 'f35aa9f6633cb8aa3b582ef8cd6f73b75d5343ef3e4c698be02be98bc0187771', 'line': 46, 'declaration': 'APFPaper5.K4.recDiag_jointQuarter'}]

import Definitions.Def_APFPaper5_K4_JointCarrier
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.recDiag_jointQuarter (p : Joint) : recDiag (jointQuarter p) = recDiag p := by sorry
