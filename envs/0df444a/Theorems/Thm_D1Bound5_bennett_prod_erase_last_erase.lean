-- Prove2me | Theorems.Thm_D1Bound5_bennett_prod_erase_last_erase
-- name    : D1Bound5.bennett_prod_erase_last_erase
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:33.290605+00:00
-- url     : https://prove2.me/theorems/fbc1e635-659a-4be3-9495-3792b1651170
-- title:
--   Bennett prod erase last erase
-- statement:
--   The same reindexing with one further local pole omitted.
-- source:
--   D1Bound5/BennettNodeRemoval.lean, lines 19-26, SHA-256 744b0d9ca6cef7f147ff8e1fb3ed54499f22a4c9c12ff289d69e5603296721b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.bennett_prod_erase_last_erase {M : Type*} [CommMonoid M] (n : ℕ)
    (j : Fin n) (f : Fin (n + 1) → M) :
    (∏ l ∈ ((Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n)).erase
      j.castSucc, f l) = ∏ l ∈ (Finset.univ : Finset (Fin n)).erase j, f l.castSucc := by sorry





end D1Bound5
end
