-- Prove2me | Theorems.Thm_APFPaper5_K4_extendsToJoint_of_map
-- name    : APFPaper5.K4.extendsToJoint_of_map
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:04:35.840197+00:00
-- url     : https://prove2.me/theorems/1d8debdf-d026-45fc-a9ef-284a9be8fe26
-- title:
--   Extends To Joint of map
-- statement:
--   A witness of ExtendsToJointMap for a Held2 map supplies a witness of ExtendsToJoint for that same map. The linearity and quarter-invariance premises remain structural assumptions about the supplied joint map; no general physical-process linearity theorem is claimed.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044,2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_record_book_linear.lean', 'sha256': 'f35aa9f6633cb8aa3b582ef8cd6f73b75d5343ef3e4c698be02be98bc0187771', 'line': 101, 'declaration': 'APFPaper5.K4.extendsToJoint_of_map'}]

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

theorem APFPaper5.K4.extendsToJoint_of_map (T : Held2 → Held2) (hT : ExtendsToJointMap T) : ExtendsToJoint T := by sorry
