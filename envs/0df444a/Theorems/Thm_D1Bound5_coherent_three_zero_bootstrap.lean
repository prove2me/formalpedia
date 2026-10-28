-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_zero_bootstrap
-- name    : D1Bound5.coherent_three_zero_bootstrap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:13.180702+00:00
-- url     : https://prove2.me/theorems/14327e8e-00d7-4fe9-a553-d9a35b200dc1
-- title:
--   Coherent three zero bootstrap
-- statement:
--   A zero actual three-anchor form forces a first terminal separation without assuming Q≥4P. This is the bootstrap used before applying the sharper separated vanishing window.
-- source:
--   D1Bound5/CoherentThreeZeroBootstrap.lean, lines 8-83, SHA-256 b54246d0d1c9cfd8828a4478b051dd30ad348a9516f72094e48c67fab1b6cf30. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_three_zero_bootstrap
    (a : Fin 3 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (A : ℝ) (hA : 0 < A) (ha : ∀ i, A ≤ ‖a i‖)
    (hP : 0 < ‖p‖) (hQ : ‖p‖ ≤ ‖q‖)
    (hAP : 9 ≤ A*‖p‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (heta : eta^2 = p*q)
    (hL : coherentQuotientForm a (coherentVandermonde3 a) p q eta = 0) :
    (∏ i, ‖a i‖)*‖p‖^2 < ‖q‖ := by sorry

end D1Bound5
end
