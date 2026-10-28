-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_parameter_form_bounds
-- name    : D1Bound5.coherent_three_parameter_form_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:32:12.16253+00:00
-- url     : https://prove2.me/theorems/3d56fa0b-564e-4028-8328-7c2e95a7983f
-- title:
--   Coherent three parameter form bounds
-- statement:
--   The complete three-anchor interpolation-parameter lemma for the actual coherent form. Exact numerical row checks are separate from the analytic proof; all remainder and branch hypotheses are discharged.
-- source:
--   D1Bound5/CoherentParameterForms.lean, lines 122-236, SHA-256 374d5b2d6781c171ef752c7123026755c8c7a83017464b5219e1a859229c8703. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions

section
open Finset

namespace D1Bound5










theorem _root_.D1Bound5.coherent_three_parameter_form_bounds
    (a : Fin 3 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (A H lam U : ℝ) (hA : 0 < A) (ha : ∀ i, A ≤ ‖a i‖)
    (hP : 0 < ‖p‖) (hQ : 4*‖p‖ ≤ ‖q‖) (hPQ : 10000 < ‖p‖*‖q‖)
    (hH : 1 < H) (hAP : H ≤ A*‖p‖) (heta : eta^2 = p*q)
    (hell : 0 < coherentThreeLowerConstant H) (hu : 0 < coherentThreeUpperConstant H)
    (hlam : 100*coherentThreeUpperConstant H/99 < lam)
    (hwindowLow : 5 < 100/(201*coherentThreeUpperConstant H))
    (hwindowHigh : 100/(199*coherentThreeLowerConstant H) < U) :
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ <
        51*‖coherentVandermonde3 a‖/(100*‖coherentTerminalRoot p q eta‖) +
          lam*‖coherentVandermonde3 a‖*‖coherentTerminalRoot p q eta‖ /
            ((∏ i, ‖a i‖)*‖p‖^3) ∧
      (coherentQuotientForm a (coherentVandermonde3 a) p q eta = 0 →
        5*(∏ i, ‖a i‖)*‖p‖^2 < ‖q‖ ∧
          ‖q‖ < U*(∏ i, ‖a i‖)*‖p‖^2) := by sorry

end D1Bound5
end
