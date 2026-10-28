-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedMatrix_det_remove_last
-- name    : D1Bound5.bennettClearedMatrix_det_remove_last
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:26.387989+00:00
-- url     : https://prove2.me/theorems/7f75dfb3-d66b-4d70-b741-008738e569ce
-- title:
--   Bennett Cleared Matrix det remove last
-- statement:
--   Exact determinant reduction at the removed node. Both directions of every new node difference are retained, so this identity contains its full sign.
-- source:
--   D1Bound5/BennettNodeRemoval.lean, lines 41-99, SHA-256 744b0d9ca6cef7f147ff8e1fb3ed54499f22a4c9c12ff289d69e5603296721b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]








theorem _root_.D1Bound5.bennettClearedMatrix_det_remove_last
    (n : ℕ) (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (k : ℕ) (hk : 1 ≤ k) (ν : F) :
    (bennettClearedMatrix a k ν).det.eval (-a (Fin.last n)) =
      Ring.choose ((k : F) + ν) k *
        (∏ j : Fin n, ((a (Fin.last n) - a j.castSucc)⁻¹) ^ k) *
        (∏ j : Fin n, ((a j.castSucc - a (Fin.last n))⁻¹) ^ k) *
        (bennettClearedMatrix (fun j : Fin n ↦ a j.castSucc) k
          (ν - (k : F))).det.eval (-a (Fin.last n)) := by sorry

end D1Bound5
end
