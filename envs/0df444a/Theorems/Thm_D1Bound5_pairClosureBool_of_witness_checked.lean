-- Prove2me | Theorems.Thm_D1Bound5_pairClosureBool_of_witness_checked
-- name    : D1Bound5.pairClosureBool_of_witness_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:32:47.403459+00:00
-- url     : https://prove2.me/theorems/c535cbcd-9e52-4f27-ad14-359cfe3f1191
-- title:
--   Pair Closure Bool of witness checked
-- statement:
--   A witness certificate proves the original Boolean closure certificate. Consumers such as `small_pair_graph_excludes_three_full_ring` need no change.
-- source:
--   D1Bound5/PairClosureWitness.lean, lines 127-148, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.pairClosureBool_of_witness_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b r0 : QuadInt tau nu)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (witnesses : List (PairRootWitness tau nu))
    (hcheck : pairClosureWitnessBool a b r0 bound vertices witnesses = true) :
    pairClosureBool a b bound vertices = true := by sorry

end D1Bound5
end
