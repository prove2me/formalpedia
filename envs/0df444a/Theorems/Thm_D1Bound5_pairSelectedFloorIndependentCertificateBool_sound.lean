-- Prove2me | Theorems.Thm_D1Bound5_pairSelectedFloorIndependentCertificateBool_sound
-- name    : D1Bound5.pairSelectedFloorIndependentCertificateBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:04.071346+00:00
-- url     : https://prove2.me/theorems/46e199e5-1fdf-45d2-8609-2758d89def16
-- title:
--   Pair Selected Floor Independent Certificate Bool sound
-- statement:
--   Auxiliary result `pairSelectedFloorIndependentCertificateBool_sound` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairSelectedFloorWitnesses.lean, lines 126-136, SHA-256 5627d261d76c8200c3ce7a8601856a8cef8aa9e7be044b0ebf81c7f060ce8b74. Project: https://github.com/tomislav-math/d1-bound5-lean

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











theorem _root_.D1Bound5.pairSelectedFloorIndependentCertificateBool_sound {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairSelectedFloorIndependentCertificateBool sieve vertices cached rows = true) :
    pairCachedIndependentCertificateBool sieve vertices cached = true := by sorry



end D1Bound5
end
