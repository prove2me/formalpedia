-- Prove2me | Theorems.Thm_D1Bound5_UnitPairArithmeticModel_pellIntegerSquare
-- name    : D1Bound5.UnitPairArithmeticModel.pellIntegerSquare
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:14.409436+00:00
-- url     : https://prove2.me/theorems/ba0ff48e-5892-4c56-98a0-5dfa5942ed86
-- title:
--   Unit Pair Arithmetic Model — pell Integer Square
-- statement:
--   Convert actual full-ring squares of ordinary integers using the same fixed d as the Pell description, including zero and negative radicands.
-- source:
--   D1Bound5/PellFiniteCertificate.lean, lines 39-49, SHA-256 dcc2fd88b881b2c8eafcbde15c1cb33b51af6fe491a0856432d4dcd395c5e1ed. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.UnitPairArithmeticModel.pellIntegerSquare
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (M : UnitPairArithmeticModel (𝓞 K))
    (m : ℤ) (hs : ∃ r : 𝓞 K, r*r = (m : 𝓞 K)) : PellIntegerSquare M.d m := by sorry





end D1Bound5
end
