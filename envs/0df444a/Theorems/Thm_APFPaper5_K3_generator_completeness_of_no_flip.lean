-- Prove2me | Theorems.Thm_APFPaper5_K3_generator_completeness_of_no_flip
-- name    : APFPaper5.K3.generator_completeness_of_no_flip
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:00:47.914641+00:00
-- url     : https://prove2.me/theorems/cac9561d-d5d2-456d-af6a-61fb2585dc97
-- title:
--   Generator completeness of no flip
-- statement:
--   Assume hroot and a supplied admitted set containing every generated map, closed under composition, consisting of real-linear totalCost-preserving unseen maps, and excluding rateFlip. Every admitted map is generated. The admitted set, its closure, all-map properties and flip exclusion are hypotheses; no physical exclusion is certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_completeness_without_flip.lean', 'sha256': 'f6d0903191d4ff44aa087dc3396ad27e025c7f3a9e30d9a31d0b19ac023b7480', 'line': 81, 'declaration': 'APFPaper5.K3.generator_completeness_of_no_flip'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.generator_completeness_of_no_flip
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hflip : rateFlip ∉ Adm) : ∀ T ∈ Adm, BuiltFromTurns T := by sorry
