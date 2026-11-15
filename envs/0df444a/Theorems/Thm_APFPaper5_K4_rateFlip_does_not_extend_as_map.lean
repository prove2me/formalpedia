-- Prove2me | Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend_as_map
-- name    : APFPaper5.K4.rateFlip_does_not_extend_as_map
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:05:36.220288+00:00
-- url     : https://prove2.me/theorems/7f4bfed4-234e-4086-9aa9-c01dd5a40b6b
-- title:
--   Rate flip has no specified linear joint extension
-- statement:
--   There is no ExtendsToJointMap witness for rateFlip under the supplied joint carrier and recDiag product-compatibility definition. The linearity and quarter-invariance premises remain structural assumptions about the supplied joint map; no general physical-process linearity theorem is claimed.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044,2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_record_book_linear.lean', 'sha256': 'f35aa9f6633cb8aa3b582ef8cd6f73b75d5343ef3e4c698be02be98bc0187771', 'line': 106, 'declaration': 'APFPaper5.K4.rateFlip_does_not_extend_as_map'}]

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

theorem APFPaper5.K4.rateFlip_does_not_extend_as_map : ¬ ExtendsToJointMap rateFlip := by sorry
