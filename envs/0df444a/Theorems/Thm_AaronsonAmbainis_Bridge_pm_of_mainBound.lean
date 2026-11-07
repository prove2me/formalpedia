-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_pm_of_mainBound
-- name    : AaronsonAmbainis.Bridge.pm_of_mainBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:37.686197+00:00
-- url     : https://prove2.me/theorems/ee326a58-968f-417d-9be8-41152b5d9ba9
-- title:
--   Bridge: pm of main Bound
-- statement:
--   A bound of the kind of the main theorem for polynomials on the cube `{1,-1}^n` which are
--   bounded by `1`: `3 ε^5 ≤ C d^12 Inf_i(p)²`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L179-L193
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L179-L193

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.pm_of_mainBound {C : ℝ} (h : MainBound C) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 := by sorry
