-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_printedConcl_iff
-- name    : AaronsonAmbainis.Bridge.printedConcl_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:19.837054+00:00
-- url     : https://prove2.me/theorems/755b8ab4-98be-4170-9c55-b0694eea495e
-- title:
--   Bridge: printed Concl iff
-- statement:
--   The printed conclusion is literally the conclusion of `RowBound`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L54-L58
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L54-L58

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.printedConcl_iff {n : ℕ} (f : Cube (Fin n) → ℝ) (d : ℕ) :
    PrintedConcl f d ↔ ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) := by sorry
