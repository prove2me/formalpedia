-- Prove2me | Theorems.Thm_APFPaper5_K4_sync_part_is_sync
-- name    : APFPaper5.K4.sync_part_is_sync
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:56:27.688974+00:00
-- url     : https://prove2.me/theorems/962adaac-3e0f-44ad-bbdc-30469c58d66c
-- title:
--   Sync part is sync
-- statement:
--   For commuting additive square-minus-one maps J1 and J2, their actions agree on x minus J1(J2(x)). On a bare additive group the displayed decomposition is of twice x, not necessarily x: division by two is not assumed. FirstOrder elimination retains C not equal to one, additivity and the strong independence hypothesis.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2058-2090,2213-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_two_sheets.lean', 'sha256': 'daefe15c4a2644392251062582e7028fc39049ca04c2e6ebff5c072fc52122d5', 'line': 46, 'declaration': 'APFPaper5.K4.sync_part_is_sync'}]

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

theorem APFPaper5.K4.sync_part_is_sync (J1 J2 : V →+ V) (hsq1 : ∀ x : V, J1 (J1 x) = -x)
    (hsq2 : ∀ x : V, J2 (J2 x) = -x) (hcomm : ∀ x : V, J1 (J2 x) = J2 (J1 x)) (x : V) :
    J1 (x - J1 (J2 x)) = J2 (x - J1 (J2 x)) := by sorry
