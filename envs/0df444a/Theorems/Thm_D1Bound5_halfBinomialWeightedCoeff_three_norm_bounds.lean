-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_three_norm_bounds
-- name    : D1Bound5.halfBinomialWeightedCoeff_three_norm_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:10.454474+00:00
-- url     : https://prove2.me/theorems/f74769ed-81c7-4274-8d14-49d34e37c06a
-- title:
--   Half Binomial Weighted Coeff three norm bounds
-- statement:
--   Both sharp elementary degree-three bounds under quarter-size terminal separation. The lower bound is a reverse triangle estimate on each of the two factors, so no phase or square-root sign is assumed.
-- source:
--   D1Bound5/CoherentThreeParameters.lean, lines 34-79, SHA-256 ca0fac013bc4ef76939f023e46143eabcee36be640a6d47b13f0373264757949. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions

section
open Finset

noncomputable section

namespace D1Bound5










theorem _root_.D1Bound5.halfBinomialWeightedCoeff_three_norm_bounds
    (x y : ℂ) (P : ℝ) (hP : 0 < P)
    (hx : ‖x‖ = 1/P) (hy : ‖y‖ ≤ 1/(4*P)) :
    45/(1024*P^3) ≤ ‖halfBinomialWeightedCoeff x y 3‖ ∧
    ‖halfBinomialWeightedCoeff x y 3‖ ≤ 85/(1024*P^3) := by sorry







end D1Bound5
end
