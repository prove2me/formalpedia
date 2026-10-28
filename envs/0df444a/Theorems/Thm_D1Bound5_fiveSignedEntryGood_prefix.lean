-- Prove2me | Theorems.Thm_D1Bound5_fiveSignedEntryGood_prefix
-- name    : D1Bound5.fiveSignedEntryGood_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:32.468811+00:00
-- url     : https://prove2.me/theorems/1d43a5ac-2e1e-4364-8fcf-50eab716ec0c
-- title:
--   Five Signed Entry Good prefix
-- statement:
--   A simultaneous five-entry choice retains the existing mixed prefix predicate.
-- source:
--   D1Bound5/ProductFiveCompatibleSigns.lean, lines 164-192, SHA-256 7ef326eadce635a2fc8001d19ab9a7846a67febccdcf6d3cfe50963ad72c4cef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions

section
namespace D1Bound5












theorem _root_.D1Bound5.fiveSignedEntryGood_prefix {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hgood : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) :
    ∀ i j : Fin 4, i ≠ j →
      MixedSignedEntryGood f (fun k => a (Fin.castAdd 1 k))
        (fun k => u (Fin.castAdd 1 k)) i j
        (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) := by sorry





open scoped NumberField
open Module








end D1Bound5
end
