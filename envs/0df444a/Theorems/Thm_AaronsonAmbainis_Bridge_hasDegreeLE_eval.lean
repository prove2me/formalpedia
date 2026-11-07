-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:52.750457+00:00
-- url     : https://prove2.me/theorems/e6318bb5-0e71-4f8c-819a-be197c3f5465
-- title:
--   Bridge: has Degree LE eval
-- statement:
--   Restricting a polynomial of total degree `≤ d` along a point map whose coordinates have
--   degree `≤ 1` gives a function of degree `≤ d`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L31-L48
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L31-L48

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_eval {v : Cube ι → ι → ℝ} (hv : ∀ i, HasDegreeLE (fun x => v x i) 1)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x => MvPolynomial.eval (v x) p) d := by sorry
