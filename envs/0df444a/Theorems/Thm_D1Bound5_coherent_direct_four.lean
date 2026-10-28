-- Prove2me | Theorems.Thm_D1Bound5_coherent_direct_four
-- name    : D1Bound5.coherent_direct_four
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:51:47.212045+00:00
-- url     : https://prove2.me/theorems/90f71db0-5180-4306-8b7c-5c1a4ed1d270
-- title:
--   Coherent direct four
-- statement:
--   The complete direct-four lemma for actual coherent roots.
-- source:
--   D1Bound5/CoherentDirectFour.lean, lines 138-206, SHA-256 f298f052fa0e8fad59aa2ae6bf4f0b0845732c38cbe5210b92112fe6b28bc147. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.coherent_direct_four
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hP : 1000 ≤ ‖p‖) (hQ : 1000*‖p‖ ≤ ‖q‖)
    (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖ <
        13*‖a 1‖*‖a 2‖^2*‖a 3‖^3/‖coherentTerminalRoot p q eta‖ +
          49*‖a 2‖*‖a 3‖^2*‖coherentTerminalRoot p q eta‖/(50*‖a 0‖*‖p‖^4) ∧
      (coherentQuotientForm a (coherentVandermonde4 a) p q eta = 0 →
        10*‖a 0‖*‖a 1‖*‖a 2‖*‖a 3‖*‖p‖^3 < ‖q‖ ∧
          ‖q‖ < 17*‖a 0‖*‖a 1‖*‖a 2‖*‖a 3‖*‖p‖^3) := by sorry

end D1Bound5
end
