-- Prove2me | Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
-- name    : APFPaper5.K3.commuting_is_combination_of_built
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:48:44.398728+00:00
-- url     : https://prove2.me/theorems/45bfcb99-5569-4424-b7e0-bdecb061c926
-- title:
--   Commuting is combination of built
-- statement:
--   Every real-linear map commuting with the common quarter turn is a real linear combination of the eight explicit maps displayed in the formal statement. This span result needs neither cost preservation nor hroot. This classifies model endomorphisms. It does not identify the physical represented observable algebra or prove its J-module closure, faithful action, classification import, or actual generator admission. Keep hroot wherever bound.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_generator_completeness.lean', 'sha256': '72583ee936562d54c86c90f3789e818a94941ead02b97379070210cffa87cab0', 'line': 131, 'declaration': 'APFPaper5.K3.commuting_is_combination_of_built'}]

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

theorem APFPaper5.K3.commuting_is_combination_of_built (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 : ℝ, ∀ h : Held2, T h =
      add2
        (add2 (add2 (smul2 x1 h) (smul2 x2 (commonTurn 0 1 h)))
          (add2 (smul2 x3 (relativeTurn (-1) 0 h))
            (smul2 x4 (commonTurn 0 1 (relativeTurn (-1) 0 h)))))
        (add2 (add2 (smul2 x5 (mix 0 1 h)) (smul2 x6 (commonTurn 0 1 (mix 0 1 h))))
          (add2 (smul2 x7 (mix 0 1 (relativeTurn (-1) 0 h)))
            (smul2 x8 (commonTurn 0 1 (mix 0 1 (relativeTurn (-1) 0 h)))))) := by sorry
