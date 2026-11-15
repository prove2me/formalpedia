-- Prove2me | Theorems.Thm_APFPaper5_K4_firstOrder_coturn_kills_other_sheet
-- name    : APFPaper5.K4.firstOrder_coturn_kills_other_sheet
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:45:50.211192+00:00
-- url     : https://prove2.me/theorems/1b081550-2fc8-4267-b899-a6d3b11a07ee
-- title:
--   Conditional cyclic-span elimination of a fixed component
-- statement:
--   Let an additive T satisfy the stated second-order recurrence at x and fix y. If C differs from one, x and Tx have the stated independence from the line through y, and FirstOrder holds at x+y, then y is zero. On a bare additive group the displayed decomposition is of twice x, not necessarily x: division by two is not assumed. FirstOrder elimination retains C not equal to one, additivity and the strong independence hypothesis.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2058-2090,2213-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_two_sheets.lean', 'sha256': 'daefe15c4a2644392251062582e7028fc39049ca04c2e6ebff5c072fc52122d5', 'line': 75, 'declaration': 'APFPaper5.K4.firstOrder_coturn_kills_other_sheet'}]

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

theorem APFPaper5.K4.firstOrder_coturn_kills_other_sheet [Module ℝ V] (T : V → V)
    (hadd : ∀ a b : V, T (a + b) = T a + T b) (x y : V) (C : ℝ) (hC : C ≠ 1)
    (hx : T (T x) = (-1 : ℝ) • x + (2 * C) • T x) (hy : T y = y)
    (hind : ∀ a b c : ℝ, a • x + b • T x = c • y → a = 0 ∧ b = 0)
    (hfo : APFPaper5.K3.FirstOrder T (x + y)) : y = 0 := by sorry
