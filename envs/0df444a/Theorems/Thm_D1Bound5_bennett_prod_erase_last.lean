-- Prove2me | Theorems.Thm_D1Bound5_bennett_prod_erase_last
-- name    : D1Bound5.bennett_prod_erase_last
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:41:38.173201+00:00
-- url     : https://prove2.me/theorems/c6c4acb7-b8e8-4eba-9669-3c020620d70c
-- title:
--   Bennett prod erase last
-- statement:
--   Products over all nodes except the last are products over the prefix.
-- source:
--   D1Bound5/BennettNodeRemoval.lean, lines 10-17, SHA-256 744b0d9ca6cef7f147ff8e1fb3ed54499f22a4c9c12ff289d69e5603296721b1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


theorem _root_.D1Bound5.bennett_prod_erase_last {M : Type*} [CommMonoid M] (n : ℕ)
    (f : Fin (n + 1) → M) :
    (∏ l ∈ (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n), f l) =
      ∏ l : Fin n, f l.castSucc := by sorry







end D1Bound5
end
