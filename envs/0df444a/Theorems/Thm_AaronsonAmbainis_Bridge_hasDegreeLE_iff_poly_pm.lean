-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_poly_pm
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_pm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:00.33876+00:00
-- url     : https://prove2.me/theorems/3049e5c5-5ea2-4626-9b9c-48d5bfbbdd38
-- title:
--   Bridge: has Degree LE iff poly pm
-- statement:
--   `HasDegreeLE f d` ⟺ `f` is a polynomial of total degree `≤ d` in the `±1` coordinates.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L108-L117
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L108-L117

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_pm {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (pmPt x) p := by sorry
