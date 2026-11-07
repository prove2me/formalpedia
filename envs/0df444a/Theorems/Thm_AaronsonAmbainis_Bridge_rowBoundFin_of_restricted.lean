-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBoundFin_of_restricted
-- name    : AaronsonAmbainis.Bridge.rowBoundFin_of_restricted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:32.406981+00:00
-- url     : https://prove2.me/theorems/3998fd95-2324-4c40-83d0-3d68034e2b3d
-- title:
--   Bridge: row Bound Fin of restricted
-- statement:
--   The cases `n = 0` and `d = 0` of `RowBoundFin` are trivially true, so the statement
--   restricted to `n ≥ 1`, `d ≥ 1` already gives `RowBoundFin`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L71-L82
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L71-L82

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.rowBoundFin_of_restricted
    (h : ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : Cube (Fin n) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      HasDegreeLE f d → PrintedConcl f d) : RowBoundFin := by sorry
