-- Prove2me | Theorems.Thm_APFPaper5_K4_generator_completeness_of_joint_extension
-- name    : APFPaper5.K4.generator_completeness_of_joint_extension
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:08:56.423556+00:00
-- url     : https://prove2.me/theorems/2bb442b5-ac7b-4c16-a0db-20a2aff18577
-- title:
--   Generator completeness of joint extension
-- statement:
--   Assume hroot and a supplied admitted set containing generated maps, closed under composition, satisfying linearity, totalCost preservation and common-turn invisibility, and whose every map satisfies ExtendsToJoint. Every admitted map is generated. The extension premises and synchronized joint carrier remain supplied. No full K4 construction, physical CP theorem or independent derivation of no-flip from B03 alone is certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2213-2235,2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_completeness_from_composition.lean', 'sha256': '2c2eb3428821796ae7a6dd3cce30628f7030b81be51f90ff6993ed91af3dd91e', 'line': 61, 'declaration': 'APFPaper5.K4.generator_completeness_of_joint_extension'}]

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

theorem APFPaper5.K4.generator_completeness_of_joint_extension
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hext : ∀ T ∈ Adm, ExtendsToJoint T) : ∀ T ∈ Adm, BuiltFromTurns T := by sorry
