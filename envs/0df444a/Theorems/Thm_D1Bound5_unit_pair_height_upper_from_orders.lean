-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_height_upper_from_orders
-- name    : D1Bound5.unit_pair_height_upper_from_orders
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:27.85521+00:00
-- url     : https://prove2.me/theorems/77ecebf9-b6c1-4081-9752-59334ac863ee
-- title:
--   Unit pair height upper from orders
-- statement:
--   Specialization of the ordinary envelope to the unit-pair anchors. The three logarithmic parameters are certified by exact power comparisons.
-- source:
--   D1Bound5/UnitPairHeightCutoff.lean, lines 17-49, SHA-256 0c2e2f5d6333fc3971f549ba84e0129a097627670f990f7ead321a035b9be11c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.unit_pair_height_upper_from_orders (S D Z : ℝ)
    (hS : 10000 ≤ S) (hD : 0 < D) (hZ : 1 ≤ Z) (hprod : S*D < 2*Z^2)
    (horders : ∀ k : ℕ, 1 ≤ k →
      1 < 3*S*(42*S)^k/Z+Z/(2*(27*(S-1)^2/64)^k)) :
    ordinaryLog10 D < 7*ordinaryLog10 S+617/25+
      (118401/2500)/(ordinaryLog10 S-203/100) := by sorry



end D1Bound5
end
