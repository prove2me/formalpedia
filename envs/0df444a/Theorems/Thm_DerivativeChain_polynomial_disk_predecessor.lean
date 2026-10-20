-- Prove2me | Theorems.Thm_DerivativeChain_polynomial_disk_predecessor
-- name    : DerivativeChain.polynomial_disk_predecessor
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-17T18:45:52.11335+00:00
-- url     : https://prove2.me/theorems/c3eea6bd-66ae-4e63-8c64-f87b2fed872b
-- title:
--   Unit-disk predecessor for an actual polynomial critical point
-- statement:
--   Let P be a complex polynomial of positive degree, let z satisfy P'(z)=0, and assume every zero of P lies in the closed unit disk. Then there is an actual zero w of P with
--
--   $$|w-z|^2\le1-|z|^2.$$
--
--   This supplies the polynomial root transition before applying the already accepted abstract complex barycentric predecessor lemma. Repeated roots and a critical point shared with P are included. No full-chain bound is asserted here.
-- source:
--   Derivative-zero chains: public formalization reference, R25, DerivativeChain.polynomial_disk_predecessor. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

theorem DerivativeChain.polynomial_disk_predecessor {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0)
    (hdisk : ∀ w : ℂ, P.eval w = 0 → ‖w‖ ≤ 1) :
    ∃ w : ℂ, P.eval w = 0 ∧ ‖w - z‖ ^ 2 ≤ 1 - ‖z‖ ^ 2 := by sorry
