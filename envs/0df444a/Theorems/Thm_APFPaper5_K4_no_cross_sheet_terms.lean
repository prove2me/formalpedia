-- Prove2me | Theorems.Thm_APFPaper5_K4_no_cross_sheet_terms
-- name    : APFPaper5.K4.no_cross_sheet_terms
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:54:08.141479+00:00
-- url     : https://prove2.me/theorems/09b7b0cb-2f68-43b0-b532-31be532285cd
-- title:
--   No cross sheet terms
-- statement:
--   If a real-valued form is preserved by J1 and J2 and is odd in its second argument, its value between a J1=J2 state and a J1=-J2 state is zero. On a bare additive group the displayed decomposition is of twice x, not necessarily x: division by two is not assumed. FirstOrder elimination retains C not equal to one, additivity and the strong independence hypothesis.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2058-2090,2213-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_two_sheets.lean', 'sha256': 'daefe15c4a2644392251062582e7028fc39049ca04c2e6ebff5c072fc52122d5', 'line': 35, 'declaration': 'APFPaper5.K4.no_cross_sheet_terms'}]

import Definitions.Def_APFPaper5_K3_FirstOrder
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
universe u
variable {V : Type u} [AddCommGroup V]

theorem APFPaper5.K4.no_cross_sheet_terms (J1 J2 : V → V) (B : V → V → ℝ)
    (hB1 : ∀ x y : V, B (J1 x) (J1 y) = B x y) (hB2 : ∀ x y : V, B (J2 x) (J2 y) = B x y)
    (hneg : ∀ x y : V, B x (-y) = -(B x y)) (x y : V) (hx : J1 x = J2 x) (hy : J1 y = -(J2 y)) :
    B x y = 0 := by sorry
