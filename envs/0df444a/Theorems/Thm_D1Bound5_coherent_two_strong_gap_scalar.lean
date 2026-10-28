-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_strong_gap_scalar
-- name    : D1Bound5.coherent_two_strong_gap_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:40:45.798052+00:00
-- url     : https://prove2.me/theorems/70505953-46bc-498b-a00b-b33f68e594c7
-- title:
--   Coherent two strong gap scalar
-- statement:
--   The quantitative two-anchor gap after the analytic upper bound and integral lower bound have been supplied. The root-size inputs are only the elementary consequences of `z^2=pq+1`.
-- source:
--   D1Bound5/CoherentTwoGap.lean, lines 26-68, SHA-256 9b03b858f3c9928eaa8ca4f9e63d4ac4f91f397c8d8e6a3896dbdcf15993ec4f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.coherent_two_strong_gap_scalar
    (A B P Q Z : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hP : 5 * B ≤ P)
    (hAP : 32 ≤ A * P) (hQ : 5 * A * B * P ≤ Q)
    (hPQ : 10000 < P * Q) (hZ : 0 ≤ Z)
    (hZlower : P * Q - 1 ≤ Z ^ 2) (hZupper : Z ^ 2 ≤ P * Q + 1)
    (hbound : 1 < 21 * B / (20 * Z) + Z / (2 * A * P ^ 2)) :
    A ^ 2 * P ^ 3 < (10001 / 10000 : ℝ) * Q := by sorry



end D1Bound5
end
