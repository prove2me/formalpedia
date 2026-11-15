-- Prove2me | Theorems.Thm_APFPaper5_K3_expand_of_commutes
-- name    : APFPaper5.K3.expand_of_commutes
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:50:21.466922+00:00
-- url     : https://prove2.me/theorems/c06117a8-b8ed-42a7-8ea3-6ee80bf77936
-- title:
--   Expand of commutes
-- statement:
--   Supporting result: expand of commutes. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Commuting real-linear maps are real combinations of eight explicit generated maps. With hroot, commuting cost-preserving maps factor into four generator actions; unseen linear isometries are generated or flipped-generated. Squares and explicit admitted-half assumptions give further consequences. This classifies model endomorphisms. It does not identify the physical represented observable algebra or prove its J-module closure, faithful action, classification import, or actual generator admission. Keep hroot wherever bound.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_generator_completeness.lean', 'sha256': '72583ee936562d54c86c90f3789e818a94941ead02b97379070210cffa87cab0', 'line': 119, 'declaration': 'APFPaper5.K3.expand_of_commutes'}]

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

theorem APFPaper5.K3.expand_of_commutes (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) (h : Held2) :
    T h = add2 (add2 (smul2 h.a1 (T ⟨1, 0, 0, 0⟩)) (smul2 h.a2 (commonTurn 0 1 (T ⟨1, 0, 0, 0⟩))))
      (add2 (smul2 h.b1 (T ⟨0, 0, 1, 0⟩)) (smul2 h.b2 (commonTurn 0 1 (T ⟨0, 0, 1, 0⟩)))) := by sorry
