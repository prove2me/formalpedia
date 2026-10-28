-- Prove2me | Theorems.Thm_D1Bound5_smallPairNoTriangle_22_checked
-- name    : D1Bound5.smallPairNoTriangle_22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:14.581407+00:00
-- url     : https://prove2.me/theorems/b7ad9124-bf00-4539-8417-0423e8153e17
-- title:
--   Small Pair No Triangle 22 checked
-- statement:
--   Auxiliary result `smallPairNoTriangle_22_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphTriangle22.lean, lines 13-17, SHA-256 58638067b16baf712fde2bbf74290c3f56092c20baf1439abf609ad558706acb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_003
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairNoTriangle_22_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_1 smallPairLarge_22 = true := by sorry

end D1Bound5
end
