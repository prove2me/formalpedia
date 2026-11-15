-- Prove2me | Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
-- name    : APFPaper5.K3.admitted_is_built_or_flipped
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:47:46.425987+00:00
-- url     : https://prove2.me/theorems/3407ebef-5fe0-4a4f-973b-2bd63de9b1be
-- title:
--   Admitted is built or flipped
-- statement:
--   Supporting result: admitted is built or flipped. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Commuting real-linear maps are real combinations of eight explicit generated maps. With hroot, commuting cost-preserving maps factor into four generator actions; unseen linear isometries are generated or flipped-generated. Squares and explicit admitted-half assumptions give further consequences. This classifies model endomorphisms. It does not identify the physical represented observable algebra or prove its J-module closure, faithful action, classification import, or actual generator admission. Keep hroot wherever bound.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_generator_completeness.lean', 'sha256': '72583ee936562d54c86c90f3789e818a94941ead02b97379070210cffa87cab0', 'line': 201, 'declaration': 'APFPaper5.K3.admitted_is_built_or_flipped'}]

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

theorem APFPaper5.K3.admitted_is_built_or_flipped (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) (hcost : PreservesTotalCost T)
    (hun : CommonTurnUnseenAfter T) :
    BuiltFromTurns T ∨ BuiltFromTurns (fun h => rateFlip (T h)) := by sorry
