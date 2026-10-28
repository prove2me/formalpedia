-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_norm_lt
-- name    : D1Bound5.coherent_two_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:56.467954+00:00
-- url     : https://prove2.me/theorems/71edf25f-b27f-4f32-a3b3-2f8c742a33d0
-- title:
--   Coherent two norm lt
-- statement:
--   The manuscript's quantitative two-anchor upper estimate for the actual coherent quotient form and its actual terminal square root. The tail and branch estimates are proved internally.
-- source:
--   D1Bound5/CoherentTwoUpper.lean, lines 144-243, SHA-256 48f29479abf4d160e2b566ed3b872b4c44625f1795d166a6ef4424ed0069adec. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset

namespace D1Bound5










theorem _root_.D1Bound5.coherent_two_norm_lt
    (a : Fin 2 → ℂ) (p q eta : ℂ) (hinj : Function.Injective a)
    (hA : 0 < ‖a 0‖) (hP : 0 < ‖p‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hAP : 32 ≤ ‖a 0‖ * ‖p‖) (hQ : 4 * ‖p‖ ≤ ‖q‖)
    (hPQ : 10000 < ‖p‖ * ‖q‖) (heta : eta ^ 2 = p * q) :
    ‖coherentQuotientForm a (a 0 - a 1) p q eta‖ <
      21 * ‖a 1‖ / (20 * ‖coherentTerminalRoot p q eta‖) +
        ‖coherentTerminalRoot p q eta‖ / (2 * ‖a 0‖ * ‖p‖ ^ 2) := by sorry

end D1Bound5
end
