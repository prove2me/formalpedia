-- Prove2me | Theorems.Thm_APFB01_recorded_map_is_built_or_flipped
-- name    : APFB01.recorded_map_is_built_or_flipped
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:58:33.136454+00:00
-- url     : https://prove2.me/theorems/42e1e740-20fe-4a2d-809b-5e551841be96
-- title:
--   Descent restricts supplied carrier maps
-- statement:
--   Assume real linearity, totalCost preservation, descent of all post-map profile equality predicates, and nonnegative real square roots (hroot). Then T is BuiltFromTurns or rateFlip composed after T is BuiltFromTurns. hfact is explicit descent on a supplied model profile. This is not full B01 at its original physical domain.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044'}, {'path': 'source/Theorems/Thm_APFB01_admitted_maps.lean', 'sha256': '6dbd554a9da5fbe35a89ef9ead8c940a9cc384570b5bc18f2398f5215d10c9a2', 'line': 35, 'declaration': 'APFB01.recorded_map_is_built_or_flipped'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Definitions.Def_APF_B01_DeclaredInput
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFB01_unseen_turn_changes_no_fact
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half

set_option autoImplicit false

open APFPaper5.K3 in
theorem APFB01.recorded_map_is_built_or_flipped
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (T : Held2 → Held2)
    (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T)
    (hfact : ∀ P : ℝ × ℝ × (ℝ × ℝ × ℝ) → Prop,
      APFB01.Descends plainAfterTurn (fun h : Held2 => plainAfterTurn (T h) = P)) :
    BuiltFromTurns T ∨ BuiltFromTurns (fun h => rateFlip (T h)) := by sorry
