-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_general_scalar
-- name    : D1Bound5.coherent_three_general_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:40.832558+00:00
-- url     : https://prove2.me/theorems/982774ac-e32d-4f92-89b6-e3e349cf38b2
-- title:
--   Coherent three general scalar
-- statement:
--   Scalar conversion with comfortable rational margins; the stronger tail envelope above yields `96/35 < 3` for the second contribution.
-- source:
--   D1Bound5/CoherentThreeGeneral.lean, lines 123-164, SHA-256 3d70781b1840256782f08bbde98695e566d97e604c0ab97a7731d5a9f2432486. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.coherent_three_general_scalar
    (A B S P Q E Z D d L : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hS : 0 < S) (hP : 0 < P) (hQ : 0 < Q)
    (hE : 0 < E) (hZ : 0 < Z) (hd0 : 0 ≤ d)
    (hD : D ≤ 8 * B * S ^ 2) (hEsq : E ^ 2 = P * Q)
    (hZlo : (35 / 36 : ℝ) * E < Z) (hZhi : Z < (37 / 36 : ℝ) * E)
    (hd : d < 36 / (71 * P * Q))
    (hL : L ≤ D * E * (d + (1 / (3 * P ^ 3)) / (A * B * S))) :
    L < 5 * B * S ^ 2 / Z + 3 * S * Z / (A * P ^ 3) := by sorry



end D1Bound5
end
