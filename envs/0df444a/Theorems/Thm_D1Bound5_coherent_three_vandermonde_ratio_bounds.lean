-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_vandermonde_ratio_bounds
-- name    : D1Bound5.coherent_three_vandermonde_ratio_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:59:10.254794+00:00
-- url     : https://prove2.me/theorems/7b47fa25-c2ae-4c12-9b46-0b7ec6a88562
-- title:
--   Coherent three vandermonde ratio bounds
-- statement:
--   The normalized Vandermonde factor in the retained estimate is positive and at most eight for ordered nonzero distinct anchors.
-- source:
--   D1Bound5/CoherentRetainedAnalyticData.lean, lines 7-39, SHA-256 e4a665d10b2869f821502c2c77658404842057b13044350eb4f7b226404c0728. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_three_vandermonde_ratio_bounds
    (a : Fin 3 → ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖) :
    0 < ‖coherentVandermonde3 a‖/(‖a 1‖*‖a 2‖^2) ∧
      ‖coherentVandermonde3 a‖/(‖a 1‖*‖a 2‖^2) ≤ 8 := by sorry



end D1Bound5
end
