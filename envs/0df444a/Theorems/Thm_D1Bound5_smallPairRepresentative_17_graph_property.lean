-- Prove2me | Theorems.Thm_D1Bound5_smallPairRepresentative_17_graph_property
-- name    : D1Bound5.smallPairRepresentative_17_graph_property
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:26:22.369309+00:00
-- url     : https://prove2.me/theorems/a31cbb6a-713e-4c56-a242-f851e1c6343f
-- title:
--   Small Pair Representative 17 graph property
-- statement:
--   The full triangle exclusion for manuscript representative 17.
-- source:
--   D1Bound5/SmallPairRepresentativeProperties.lean, lines 250-263, SHA-256 6d91ecadbf268974200a4e7e5af3072ebb818b8de5c7dae6b1c9885553a2067e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt


































theorem _root_.D1Bound5.smallPairRepresentative_17_graph_property
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 2 ≃+* 𝓞 K) :
    SmallPairGraphProperty {smallPairA_17,smallPairB_17} := by sorry































































end D1Bound5
end
