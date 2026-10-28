-- Prove2me | Theorems.Thm_D1Bound5_tripleExtensionFilter_of_checked
-- name    : D1Bound5.tripleExtensionFilter_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:53.479897+00:00
-- url     : https://prove2.me/theorems/7e72db53-66eb-46a3-ad82-982ea7fb7fe5
-- title:
--   Triple Extension Filter of checked
-- statement:
--   Auxiliary result `tripleExtensionFilter_of_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 192-201, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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

































theorem _root_.D1Bound5.tripleExtensionFilter_of_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b c : QuadInt tau nu)
    (vertices allowed : List (QuadInt tau nu))
    (hcheck : tripleExtensionFilterBool a b c vertices allowed = true)
    {z : QuadInt tau nu} (hz : z ∈ vertices)
    (h0 : z ≠ 0) (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c)
    (hs : ∃ r, r*r = c*z+1) : z ∈ allowed := by sorry

end D1Bound5
end
