-- Prove2me | Theorems.Thm_D1Bound5_UnitPairArithmeticModel_four_extensions_real
-- name    : D1Bound5.UnitPairArithmeticModel.four_extensions_real
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:20:06.830248+00:00
-- url     : https://prove2.me/theorems/b3b29470-5587-4505-b9d1-ea671131dada
-- title:
--   Unit Pair Arithmetic Model — four extensions real
-- statement:
--   Among four mutually compatible extensions of the unit pair, every extension is real. All axis, parity and discreteness inputs are supplied by the single arithmetic model and the actual square witnesses.
-- source:
--   D1Bound5/UnitPairRealReduction.lean, lines 61-121, SHA-256 e4a826c7ab16daad28ce995ba069b7132c5a664679a6e2cb5595024816c481ec. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairRealReduction_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5












theorem _root_.D1Bound5.UnitPairArithmeticModel.four_extensions_real
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (M : UnitPairArithmeticModel R) (f : R →+* ℂ)
    (hdiscrete : ∀ z : R, z ≠ 0 → 1 ≤ ‖f z‖)
    (z : Fin 4 → R) (hz : ∀ i, z i ≠ 0)
    (hroots : ∀ i, (∃ r : R, r^2 = 1-z i) ∧ (∃ r : R, r^2 = 1+z i))
    (hpair : ∀ i j, i ≠ j → ∃ r : R, r^2 = 1+z i*z j) :
    ∀ i, UnitPairRealDescription M.d (z i) := by sorry







end D1Bound5
end
