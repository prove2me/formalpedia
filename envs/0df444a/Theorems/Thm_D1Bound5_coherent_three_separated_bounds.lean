-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_separated_bounds
-- name    : D1Bound5.coherent_three_separated_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:02.840704+00:00
-- url     : https://prove2.me/theorems/d6c675c0-dd7d-4f91-bd6e-aa5e23e1249d
-- title:
--   Coherent three separated bounds
-- statement:
--   The stronger three-anchor estimate used for the V window. The factor 3/4 comes from terminal separation and the parameter-1000 tail.
-- source:
--   D1Bound5/CoherentThreeSeparated.lean, lines 18-78, SHA-256 59ed14d9f5e2f81a9db661347cad4ddf2d3b2b7ec38892dfe2a054a970e09ed2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.coherent_three_separated_bounds
    (a : Fin 3 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖)
    (hP : 0 < ‖p‖) (hAP : 1000 ≤ ‖a 0‖*‖p‖)
    (hQ : 4*‖p‖ ≤ ‖q‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ <
      5*‖a 1‖*‖a 2‖^2/‖coherentTerminalRoot p q eta‖ +
        3*‖a 2‖*‖coherentTerminalRoot p q eta‖/(4*‖a 0‖*‖p‖^3) ∧
    (coherentQuotientForm a (coherentVandermonde3 a) p q eta = 0 →
      5*‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^2 < ‖q‖ ∧
        ‖q‖ < 15*‖a 0‖*‖a 1‖*‖a 2‖*‖p‖^2) := by sorry

end D1Bound5
end
