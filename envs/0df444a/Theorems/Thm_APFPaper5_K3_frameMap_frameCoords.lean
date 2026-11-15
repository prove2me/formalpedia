-- Prove2me | Theorems.Thm_APFPaper5_K3_frameMap_frameCoords
-- name    : APFPaper5.K3.frameMap_frameCoords
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:00:59.862206+00:00
-- url     : https://prove2.me/theorems/5a93d778-0475-4f49-a924-7127de03202e
-- title:
--   Frame Map frame Coords
-- statement:
--   Under the full carrier checklist, reconstruction from the frame coordinates of any vector returns that vector. The premise already supplies J, linear structure, orthogonality and full spanning. The representation theorem does not construct those conditions from the eight inputs.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_carrier_representation.lean', 'sha256': 'df053a1e8e923a33bdd8dbeab02a8647d6ea030130fe02332e1b7abbcc1fd19b', 'line': 103, 'declaration': 'APFPaper5.K3.frameMap_frameCoords'}]

import Definitions.Def_APFPaper5_K3_CarrierFrame
import Theorems.Thm_APFPaper5_K3_euler_core
import Theorems.Thm_APFPaper5_K3_expand_of_commutes
import Theorems.Thm_APFPaper5_K3_commuting_is_combination_of_built
import Theorems.Thm_APFPaper5_K3_generator_completeness
import Theorems.Thm_APFPaper5_K3_built_iff
import Theorems.Thm_APFPaper5_K3_admitted_is_built_or_flipped
import Theorems.Thm_APFPaper5_K3_admitted_iff
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_halves
import Theorems.Thm_APFPaper5_K3_rateFlip_has_no_admitted_half
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K3.frameMap_frameCoords (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (v : V) :
    frameMap J a b (frameCoords B J a b v) = v := by sorry
