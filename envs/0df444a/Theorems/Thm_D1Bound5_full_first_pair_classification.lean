-- Prove2me | Theorems.Thm_D1Bound5_full_first_pair_classification
-- name    : D1Bound5.full_first_pair_classification
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:11.333104+00:00
-- url     : https://prove2.me/theorems/07de21c7-a6be-479b-9a72-6223f914691e
-- title:
--   Full first pair classification
-- statement:
--   Every first pair in a full ring is rational (1,3) up to sign, or lies in the complete finite first-pair table of one of the eleven maximal models. The unused discriminant-31 table is empty, so it contributes no pairs.
-- source:
--   D1Bound5/FirstPairClassification.lean, lines 82-136, SHA-256 7439f45210b59f019ad649fd7de039e4dd3225058c8cf127213409e314835de7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt








theorem _root_.D1Bound5.full_first_pair_classification
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b : 𝓞 K)
    (hsize :
      (‖phi (a : K)‖^2 = 1 ∧ 9 ≤ ‖phi (b : K)‖^2 ∧ ‖phi (b : K)‖^2 < 64) ∨
      (‖phi (a : K)‖^2 = 2 ∧ 9 ≤ ‖phi (b : K)‖^2 ∧ ‖phi (b : K)‖^2 < 16))
    (hroot : ∃ q : 𝓞 K, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨
      ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
        (tau,nu) ∈ smallPairModels ∧
        firstPairCoordinates (e.symm a) (e.symm b) ∈ firstPairTable tau nu := by sorry

end D1Bound5
end
