-- Prove2me | Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
-- name    : APFPaper5.K3.generator_completeness_of_halves
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:51:54.205555+00:00
-- url     : https://prove2.me/theorems/eb2991b1-1140-4db7-abae-883046b863c1
-- title:
--   Generator completeness of halves
-- statement:
--   Assume hroot and a supplied admitted set of real-linear cost-preserving unseen maps, each admitting an admitted square root under composition. Then every admitted map is generated. This classifies model endomorphisms. It does not identify the physical represented observable algebra or prove its J-module closure, faithful action, classification import, or actual generator admission. Keep hroot wherever bound.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_generator_completeness.lean', 'sha256': '72583ee936562d54c86c90f3789e818a94941ead02b97379070210cffa87cab0', 'line': 247, 'declaration': 'APFPaper5.K3.generator_completeness_of_halves'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_TwoPoint
import Theorems.Thm_APFPaper5_K3_built_commutes_common
import Theorems.Thm_APFPaper5_K3_built_commutes_quarter
import Theorems.Thm_APFPaper5_K3_comp_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_built_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_built_unseen
import Theorems.Thm_APFPaper5_K3_onePlaneQuarter_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_additiveHomogeneous
import Theorems.Thm_APFPaper5_K3_rateFlip_preserves_totalCost
import Theorems.Thm_APFPaper5_K3_rateFlip_not_built
import Theorems.Thm_APFPaper5_K3_rateFlip_comp_commutes
import Theorems.Thm_APFPaper5_K3_rateFlip_rateFlip
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.generator_completeness_of_halves
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hhalf : TurnsHaveHalves Adm) : ∀ T ∈ Adm, BuiltFromTurns T := by sorry
