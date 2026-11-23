-- Prove2me | solution 1 for sum_fin_eq_sum_range_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:40:38.266248+00:00
-- url     : https://prove2.me/submissions/2e0e803f-f6f5-47e3-b478-1923a0949d80

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {R : Type*} [CommSemiring R] (m : ℕ) (c : ℕ → R) (x : R) :
    ∑ i : Fin m, x ^ (i : ℕ) * c i = ∑ i ∈ Finset.range m, c i * x ^ i := by
  simp only [mul_comm, Finset.sum_range]
