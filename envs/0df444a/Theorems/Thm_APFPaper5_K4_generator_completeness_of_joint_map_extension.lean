-- Prove2me | Theorems.Thm_APFPaper5_K4_generator_completeness_of_joint_map_extension
-- name    : APFPaper5.K4.generator_completeness_of_joint_map_extension
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:09:13.375435+00:00
-- url     : https://prove2.me/theorems/1f136761-2406-4048-baff-5d0477937269
-- title:
--   Generator completeness of joint map extension
-- statement:
--   Under the same explicit admitted-set closure and map hypotheses, with hroot and universal ExtendsToJointMap, every admitted map is generated. The extension premises and synchronized joint carrier remain supplied. No full K4 construction, physical CP theorem or independent derivation of no-flip from B03 alone is certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2213-2235,2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_completeness_from_composition.lean', 'sha256': '2c2eb3428821796ae7a6dd3cce30628f7030b81be51f90ff6993ed91af3dd91e', 'line': 70, 'declaration': 'APFPaper5.K4.generator_completeness_of_joint_map_extension'}]

import Definitions.Def_APFPaper5_K4_JointCarrier
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Theorems.Thm_APFPaper5_K4_recDiag_jointQuarter
import Theorems.Thm_APFPaper5_K4_linear_of_additive_quarter_unseen
import Theorems.Thm_APFPaper5_K4_extendsToJoint_of_map
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend_as_map
import Theorems.Thm_APFPaper5_K3_built_has_inverse
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_no_flip
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.generator_completeness_of_joint_map_extension
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hext : ∀ T ∈ Adm, ExtendsToJointMap T) : ∀ T ∈ Adm, BuiltFromTurns T := by sorry
