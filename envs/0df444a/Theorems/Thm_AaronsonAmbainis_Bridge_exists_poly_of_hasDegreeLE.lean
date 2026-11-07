-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_exists_poly_of_hasDegreeLE
-- name    : AaronsonAmbainis.Bridge.exists_poly_of_hasDegreeLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:47.282201+00:00
-- url     : https://prove2.me/theorems/b2ba62be-5800-4ce0-9e00-a0c25cc8cc5b
-- title:
--   Bridge: exists poly of has Degree LE
-- statement:
--   A function of degree `≤ d` is the restriction of a polynomial of total degree `≤ d` in the
--   coordinates `v x i`, as soon as the sign `(-1)^{x_i}` is an affine function of `v x i`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L70-L93
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean#L70-L93

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Definitions.Def_AaronsonAmbainis_Bridge_Poly
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.exists_poly_of_hasDegreeLE {v : Cube ι → ι → ℝ} {a b : ℝ}
    (hv : ∀ x i, (if x i then (-1 : ℝ) else 1) = a + b * v x i)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (v x) p := by sorry
