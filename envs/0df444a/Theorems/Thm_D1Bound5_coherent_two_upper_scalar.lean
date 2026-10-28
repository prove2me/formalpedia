-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_upper_scalar
-- name    : D1Bound5.coherent_two_upper_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:15.158721+00:00
-- url     : https://prove2.me/theorems/dbbe7ad6-361f-45ae-8f26-7e7214aa6a0a
-- title:
--   Coherent two upper scalar
-- statement:
--   A scalar conversion of the exact coherent estimate to the two explicit terms in the manuscript.
-- source:
--   D1Bound5/CoherentTwoUpper.lean, lines 101-142, SHA-256 48f29479abf4d160e2b566ed3b872b4c44625f1795d166a6ef4424ed0069adec. Project: https://github.com/tomislav-math/d1-bound5-lean

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

namespace D1Bound5








theorem _root_.D1Bound5.coherent_two_upper_scalar
    (A B P Q E Z D d F L : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) (hQ : 0 < Q)
    (hE : 0 < E) (hZ : 0 < Z) (hD0 : 0 ≤ D) (hd0 : 0 ≤ d) (hF0 : 0 ≤ F)
    (hD : D ≤ 2 * B) (hEsq : E ^ 2 = P * Q)
    (hZlo : (99 / 100 : ℝ) * E < Z) (hZhi : Z < (101 / 100 : ℝ) * E)
    (hd : d < 100 / (199 * P * Q)) (hF : F ≤ 7 / (32 * P ^ 2))
    (hL : L ≤ D * E * (d + F / (A * B))) :
    L < 21 * B / (20 * Z) + Z / (2 * A * P ^ 2) := by sorry



end D1Bound5
end
