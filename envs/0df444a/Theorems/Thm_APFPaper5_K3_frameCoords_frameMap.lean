-- Prove2me | Theorems.Thm_APFPaper5_K3_frameCoords_frameMap
-- name    : APFPaper5.K3.frameCoords_frameMap
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:00:57.900521+00:00
-- url     : https://prove2.me/theorems/b9165cad-1720-450d-b3de-77fd66c75969
-- title:
--   Frame Coords frame Map
-- statement:
--   Under the full carrier checklist, reading the coordinates of a reconstructed Held2 state returns those same coordinates. The premise already supplies J, linear structure, orthogonality and full spanning. The representation theorem does not construct those conditions from the eight inputs.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_carrier_representation.lean', 'sha256': 'df053a1e8e923a33bdd8dbeab02a8647d6ea030130fe02332e1b7abbcc1fd19b', 'line': 94, 'declaration': 'APFPaper5.K3.frameCoords_frameMap'}]

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

theorem APFPaper5.K3.frameCoords_frameMap (B : V → V → ℝ) (J : V → V) (a b : V)
    (hc : IsTwoComponentCarrier B J a b) (h : Held2) :
    frameCoords B J a b (frameMap J a b h) = h := by sorry
