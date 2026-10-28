-- Prove2me | Theorems.Thm_D1Bound5_pairSelectedFloorIndependentBool_sound
-- name    : D1Bound5.pairSelectedFloorIndependentBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:46.625426+00:00
-- url     : https://prove2.me/theorems/444b7c15-3182-4ed0-9ec4-2da5b82a9470
-- title:
--   Pair Selected Floor Independent Bool sound
-- statement:
--   Auxiliary result `pairSelectedFloorIndependentBool_sound` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairSelectedFloorWitnesses.lean, lines 100-115, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions

section
namespace D1Bound5
open QuadInt







theorem _root_.D1Bound5.pairSelectedFloorIndependentBool_sound {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ))
    (hcheck : pairSelectedFloorIndependentBool sieve cached rows = true) :
    pairCachedIndependentBool sieve cached = true := by sorry







end D1Bound5
end
