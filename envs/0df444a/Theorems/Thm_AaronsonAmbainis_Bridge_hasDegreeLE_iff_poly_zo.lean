-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_poly_zo
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_zo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:21.153208+00:00
-- url     : https://prove2.me/theorems/6816087c-e4fd-418e-a1cb-2cd3f3408648
-- title:
--   Bridge: has Degree LE iff poly zo
-- statement:
--   `HasDegreeLE f d` ⟺ `f` is a polynomial of total degree `≤ d` in the `0/1` coordinates.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L96-L105
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L96-L105

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_iff_poly_zo {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (zoPt x) p := by sorry
