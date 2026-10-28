-- Prove2me | Theorems.Thm_D1Bound5_map_finiteQRowForm
-- name    : D1Bound5.map_finiteQRowForm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:41:19.157533+00:00
-- url     : https://prove2.me/theorems/331125dc-5178-45b3-ae17-cdeebec6baa8
-- title:
--   Map finite QRow Form
-- statement:
--   Auxiliary result `map_finiteQRowForm` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteQIntegralRows.lean, lines 36-46, SHA-256 13dbc71d3f13cc35a26b1a62808a9ec3ba2232668209833fc8f21e0bdba9f6ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]











@[simp] theorem _root_.D1Bound5.map_finiteQRowForm (f : R →+* S)
    (a b s t c z rA rB rS rT : R) (i : Fin 5) :
    f (finiteQRowForm a b s t c z rA rB rS rT i) =
      finiteQRowForm (f a) (f b) (f s) (f t) (f c)
        (f z) (f rA) (f rB) (f rS) (f rT) i := by sorry





end D1Bound5
end
