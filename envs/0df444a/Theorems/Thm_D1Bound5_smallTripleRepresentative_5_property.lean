-- Prove2me | Theorems.Thm_D1Bound5_smallTripleRepresentative_5_property
-- name    : D1Bound5.smallTripleRepresentative_5_property
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:39:58.9923+00:00
-- url     : https://prove2.me/theorems/3141cf21-12c0-4b9a-ad21-ea4051930a7b
-- title:
--   Small Triple Representative 5 property
-- statement:
--   Both finite-extension consequences for manuscript representative 5.
-- source:
--   D1Bound5/SmallTripleRepresentativeProperties.lean, lines 93-109, SHA-256 a83bbabd2bee324566724658a0b1876696641e481ed94e75fb471c1207165f52. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData5_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt












theorem _root_.D1Bound5.smallTripleRepresentative_5_property
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) :
    SmallTripleExtensionProperty
      {smallTripleAnchorA_5, smallTripleAnchorB_5, smallTripleAnchorC_5} := by sorry











end D1Bound5
end
