-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_height_cutoff_from_orders
-- name    : D1Bound5.unit_pair_height_cutoff_from_orders
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:23:24.491994+00:00
-- url     : https://prove2.me/theorems/c27ee285-60a7-48b5-96e9-4b0d26d54002
-- title:
--   Unit pair height cutoff from orders
-- statement:
--   The unit-pair cubic iteration and the actual all-order inequalities force the first extension below 10^4. The conditional input merely restricts the analytic estimates to the large regime where they apply.
-- source:
--   D1Bound5/UnitPairHeightCutoff.lean, lines 51-72, SHA-256 0c2e2f5d6333fc3971f549ba84e0129a097627670f990f7ead321a035b9be11c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5








theorem _root_.D1Bound5.unit_pair_height_cutoff_from_orders (S D Z : ℝ)
    (hS : 0 < S) (hD : 0 < D) (hZ : 1 ≤ Z) (hprod : S*D < 2*Z^2)
    (hgrowth : S^27/8192 < D)
    (horders : 10000 ≤ S → ∀ k : ℕ, 1 ≤ k →
      1 < 3*S*(42*S)^k/Z+Z/(2*(27*(S-1)^2/64)^k)) : S < 10000 := by sorry

end D1Bound5
end
