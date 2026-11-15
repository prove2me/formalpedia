-- Prove2me | Theorems.Thm_APFPaper5_K3_built_has_inverse
-- name    : APFPaper5.K3.built_has_inverse
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:58:32.052438+00:00
-- url     : https://prove2.me/theorems/58b11321-7fcd-43a0-aeeb-a9e8c36ea7f9
-- title:
--   Built has inverse
-- statement:
--   Every BuiltFromTurns map has a BuiltFromTurns map serving as its left and right inverse on all Held2 states. The admitted set, its closure, all-map properties and flip exclusion are hypotheses; no physical exclusion is certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_completeness_without_flip.lean', 'sha256': 'f6d0903191d4ff44aa087dc3396ad27e025c7f3a9e30d9a31d0b19ac023b7480', 'line': 45, 'declaration': 'APFPaper5.K3.built_has_inverse'}]

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

theorem APFPaper5.K3.built_has_inverse (U : Held2 → Held2) (hU : BuiltFromTurns U) :
    ∃ V : Held2 → Held2, BuiltFromTurns V ∧ (∀ h : Held2, U (V h) = h) ∧ ∀ h : Held2, V (U h) = h := by sorry
