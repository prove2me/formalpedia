-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_four_norm_bounds
-- name    : D1Bound5.halfBinomialWeightedCoeff_four_norm_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:08.578915+00:00
-- url     : https://prove2.me/theorems/074ca590-118c-480b-9e07-0e7add31a857
-- title:
--   Half Binomial Weighted Coeff four norm bounds
-- statement:
--   The exact separated degree-four coefficient estimates.
-- source:
--   D1Bound5/CoherentFourParameters.lean, lines 40-109, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentFourParameters_Definitions
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions

section
open Finset

noncomputable section

namespace D1Bound5














theorem _root_.D1Bound5.halfBinomialWeightedCoeff_four_norm_bounds
    (x y : ℂ) (P : ℝ) (hP : 0 < P)
    (hx : ‖x‖ = 1/P) (hy : ‖y‖ ≤ 1/(1000*P)) :
    coherentFourLeadingLower/P^4 ≤ ‖halfBinomialWeightedCoeff x y 4‖ ∧
    ‖halfBinomialWeightedCoeff x y 4‖ ≤ coherentFourLeadingUpper/P^4 := by sorry





end D1Bound5
end
