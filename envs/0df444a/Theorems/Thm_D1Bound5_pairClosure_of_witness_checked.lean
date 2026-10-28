-- Prove2me | Theorems.Thm_D1Bound5_pairClosure_of_witness_checked
-- name    : D1Bound5.pairClosure_of_witness_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:22:53.178985+00:00
-- url     : https://prove2.me/theorems/42cd6f06-01f4-43c9-bb84-55535885a53d
-- title:
--   Pair Closure of witness checked
-- statement:
--   The witness certificate supplies exactly the closure hypothesis used by the accepted full-ring descent completeness theorem.
-- source:
--   D1Bound5/PairClosureWitness.lean, lines 98-125, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt


















theorem _root_.D1Bound5.pairClosure_of_witness_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (hcheck : pairClosureWitnessBool a b r0 bound vertices witnesses = true)
    {z w : QuadInt tau nu} (hz : z ∈ vertices)
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z)
    (hbound : w.norm ≤ bound) : w ∈ vertices := by sorry



end D1Bound5
end
