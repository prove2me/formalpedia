-- Prove2me | Theorems.Thm_D1Bound5_coherent_elementary_norm_bounds
-- name    : D1Bound5.coherent_elementary_norm_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:02:59.60001+00:00
-- url     : https://prove2.me/theorems/9add61bf-3436-4fb0-b296-53a511f565f2
-- title:
--   Coherent elementary norm bounds
-- statement:
--   Elementary symmetric norm bounds for four ordered anchors.
-- source:
--   D1Bound5/CoherentThreeNonvanishing.lean, lines 7-41, SHA-256 20f76d470fd8a77be69b6cbe7c960d5062bc8bb2410754eb1f27bcf0090be809. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_elementary_norm_bounds
    (a : Fin 4 → ℂ)
    (h01 : ‖a 0‖ ≤ ‖a 1‖) (h12 : ‖a 1‖ ≤ ‖a 2‖) (h23 : ‖a 2‖ ≤ ‖a 3‖) :
    ‖coherentElementary2 a‖ ≤ 6 * ‖a 2‖ * ‖a 3‖ ∧
    ‖coherentElementary3 a‖ ≤ 4 * ‖a 1‖ * ‖a 2‖ * ‖a 3‖ ∧
    ‖coherentElementary4 a‖ = ‖a 0‖ * ‖a 1‖ * ‖a 2‖ * ‖a 3‖ := by sorry













end D1Bound5
end
