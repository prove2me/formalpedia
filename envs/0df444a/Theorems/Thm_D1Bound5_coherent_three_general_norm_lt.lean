-- Prove2me | Theorems.Thm_D1Bound5_coherent_three_general_norm_lt
-- name    : D1Bound5.coherent_three_general_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:32:06.581995+00:00
-- url     : https://prove2.me/theorems/c60cdaf6-ed44-44b3-8956-e21aec6b9d51
-- title:
--   Coherent three general norm lt
-- statement:
--   The general three-anchor estimate for the actual coherent form. Only ordered anchor moduli and the manuscript's size conditions remain; no auxiliary analytic approximation or remainder bound is assumed.
-- source:
--   D1Bound5/CoherentThreeGeneral.lean, lines 166-276, SHA-256 3d70781b1840256782f08bbde98695e566d97e604c0ab97a7731d5a9f2432486. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.coherent_three_general_norm_lt
    (a : Fin 3 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖) (hBS : ‖a 1‖ ≤ ‖a 2‖)
    (hP : 4 * ‖a 2‖ ≤ ‖p‖) (hAP : 9 ≤ ‖a 0‖ * ‖p‖)
    (hQ : ‖p‖ ≤ ‖q‖) (heta : eta ^ 2 = p * q) :
    ‖coherentQuotientForm a (coherentVandermonde3 a) p q eta‖ <
      5 * ‖a 1‖ * ‖a 2‖ ^ 2 / ‖coherentTerminalRoot p q eta‖ +
        3 * ‖a 2‖ * ‖coherentTerminalRoot p q eta‖ / (‖a 0‖ * ‖p‖ ^ 3) := by sorry

end D1Bound5
end
