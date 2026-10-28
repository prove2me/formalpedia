-- Prove2me | Theorems.Thm_D1Bound5_pairGraphTriangleFreeBool_of_split
-- name    : D1Bound5.pairGraphTriangleFreeBool_of_split
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:29:52.641351+00:00
-- url     : https://prove2.me/theorems/49a51f3b-34fe-4492-91a3-0c8baff5abd0
-- title:
--   Pair Graph Triangle Free Bool of split
-- statement:
--   Auxiliary result `pairGraphTriangleFreeBool_of_split` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairBipartiteCheck.lean, lines 118-125, SHA-256 d1497b46c9dcbae577d7172e6c4401388a1797e68d33ba795d4e6a6a05dd4c0c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions

section
namespace D1Bound5
open QuadInt











theorem _root_.D1Bound5.pairGraphTriangleFreeBool_of_split {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu)) (colors : ℕ)
    (hleft : pairIndependentBool sieve (pairSplitByMask vertices colors).1 = true)
    (hright : pairIndependentBool sieve (pairSplitByMask vertices colors).2 = true) :
    pairGraphTriangleFreeBool sieve vertices = true := by sorry

end D1Bound5
end
