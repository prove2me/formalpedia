-- Prove2me | solution 1 for eval_poly_from_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:21:04.588637+00:00
-- url     : https://prove2.me/submissions/411b9630-ca62-4034-b86f-1e6095a1c01a

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [CommSemiring F] (m : ℕ)
    (P_i : Fin m → Polynomial F) (y : F) :
    (poly_from_components m P_i).eval y = ∑ i : Fin m, (P_i i).eval (y ^ m) * y ^ (i : ℕ) := by
  simp [poly_from_components, Polynomial.eval_finset_sum]
