-- Prove2me | Theorems.Thm_D1Bound5_bennettDirectedProduct_succ
-- name    : D1Bound5.bennettDirectedProduct_succ
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:12.620756+00:00
-- url     : https://prove2.me/theorems/b9950958-6cd1-481b-b688-9594351b715f
-- title:
--   Bennett Directed Product succ
-- statement:
--   Splitting the ordered-pair product exposes the two directions involving the removed node and leaves the ordered-pair product on the prefix.
-- source:
--   D1Bound5/BennettDeterminantFormula.lean, lines 32-60, SHA-256 f98a83f3277331ffd79b4bad983ece2c8026e08c5e60f13dc8b325624528de0f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]








theorem _root_.D1Bound5.bennettDirectedProduct_succ (n : ℕ) (a : Fin (n + 1) → F) (k : ℕ) :
    bennettDirectedProduct a k =
      (∏ j : Fin n, ((a (Fin.last n) - a j.castSucc)⁻¹) ^ k) *
        (∏ j : Fin n, ((a j.castSucc - a (Fin.last n))⁻¹) ^ k) *
          bennettDirectedProduct (fun j : Fin n ↦ a j.castSucc) k := by sorry







end D1Bound5
end
