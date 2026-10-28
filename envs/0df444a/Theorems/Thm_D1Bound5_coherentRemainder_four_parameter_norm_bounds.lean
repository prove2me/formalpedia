-- Prove2me | Theorems.Thm_D1Bound5_coherentRemainder_four_parameter_norm_bounds
-- name    : D1Bound5.coherentRemainder_four_parameter_norm_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:43.983713+00:00
-- url     : https://prove2.me/theorems/148ac1f4-9bc4-4443-8073-ce17bcbea9b4
-- title:
--   Coherent Remainder four parameter norm bounds
-- statement:
--   Two-sided actual remainder bounds in the direct-four regime.
-- source:
--   D1Bound5/CoherentFourParameters.lean, lines 111-167, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
import Definitions.Def_D1Bound5_CoherentFourParameters_Definitions

section
open Finset

noncomputable section

namespace D1Bound5
















theorem _root_.D1Bound5.coherentRemainder_four_parameter_norm_bounds
    (a : Fin 4 → ℂ) (p q : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P) (ha : ∀ i, A ≤ ‖a i‖)
    (hp : ‖p⁻¹‖ = 1/P) (hq : ‖q⁻¹‖ ≤ 1/(1000*P))
    (hAP : 1000 ≤ A*P) :
    coherentFourLowerConstant/P^4 ≤ ‖coherentRemainder a p q‖ ∧
    ‖coherentRemainder a p q‖ ≤ coherentFourUpperConstant/P^4 := by sorry



end D1Bound5
end
