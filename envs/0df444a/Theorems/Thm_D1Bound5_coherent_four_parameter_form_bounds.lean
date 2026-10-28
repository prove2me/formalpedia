-- Prove2me | Theorems.Thm_D1Bound5_coherent_four_parameter_form_bounds
-- name    : D1Bound5.coherent_four_parameter_form_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:59:08.782454+00:00
-- url     : https://prove2.me/theorems/fa47a004-ae4e-430c-82fa-1e86e0a7525e
-- title:
--   Coherent four parameter form bounds
-- statement:
--   The actual four-anchor form with its separated-parameter constants and its exact zero-form window.
-- source:
--   D1Bound5/CoherentDirectFour.lean, lines 8-136, SHA-256 f298f052fa0e8fad59aa2ae6bf4f0b0845732c38cbe5210b92112fe6b28bc147. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.coherent_four_parameter_form_bounds
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (A : ℝ) (hA : 0 < A) (ha : ∀ i, A ≤ ‖a i‖)
    (hP : 0 < ‖p‖) (hQ : 1000*‖p‖ ≤ ‖q‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (hAP : 1000 ≤ A*‖p‖) (heta : eta^2 = p*q) :
    ‖coherentQuotientForm a (coherentVandermonde4 a) p q eta‖ <
        51*‖coherentVandermonde4 a‖/(100*‖coherentTerminalRoot p q eta‖) +
          (49/1200 : ℝ)*‖coherentVandermonde4 a‖*‖coherentTerminalRoot p q eta‖ /
            ((∏ i, ‖a i‖)*‖p‖^4) ∧
      (coherentQuotientForm a (coherentVandermonde4 a) p q eta = 0 →
        10*(∏ i, ‖a i‖)*‖p‖^3 < ‖q‖ ∧
          ‖q‖ < 17*(∏ i, ‖a i‖)*‖p‖^3) := by sorry



end D1Bound5
end
