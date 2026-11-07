-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_weights_nonneg_of_row
-- name    : AaronsonAmbainis.Bridge.weights_nonneg_of_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:21.591202+00:00
-- url     : https://prove2.me/theorems/3e7f51eb-a130-4da0-bb6a-8b6c132834bd
-- title:
--   Bridge: weights nonneg of row
-- statement:
--   Weights satisfying the first condition of `RowBound` are nonnegative (take `y = x^i`).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L112-L117
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L112-L117

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.weights_nonneg_of_row {ι : Type*} [Fintype ι] [DecidableEq ι] {f : Cube ι → ℝ}
    {c : Cube ι → ι → ℝ} (h : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) (x : Cube ι)
    (i : ι) : 0 ≤ c x i := by sorry
