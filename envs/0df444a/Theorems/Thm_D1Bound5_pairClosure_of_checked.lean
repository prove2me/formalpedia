-- Prove2me | Theorems.Thm_D1Bound5_pairClosure_of_checked
-- name    : D1Bound5.pairClosure_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:05.662069+00:00
-- url     : https://prove2.me/theorems/0ddf75b5-e64b-4cd2-9111-7c519743a49e
-- title:
--   Pair Closure of checked
-- statement:
--   Auxiliary result `pairClosure_of_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 173-182, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt





























theorem _root_.D1Bound5.pairClosure_of_checked {tau nu : ℤ} (a b : QuadInt tau nu) (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (hcheck : pairClosureBool a b bound vertices = true)
    {z w : QuadInt tau nu} (hz : z ∈ vertices)
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z)
    (hbound : w.norm ≤ bound) : w ∈ vertices := by sorry





end D1Bound5
end
