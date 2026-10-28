-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_C_seventh_power
-- name    : D1Bound5.two_small_large_C_seventh_power
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:50.813648+00:00
-- url     : https://prove2.me/theorems/6d5bcd12-b337-460d-9c91-4f10230cfd8a
-- title:
--   Two small large C seventh power
-- statement:
--   The actual direct-four inequality forces seventh-power terminal growth in the remaining small-anchor box.
-- source:
--   D1Bound5/TwoSmallLargeCScalar.lean, lines 91-131, SHA-256 804f219a120af73973c5200ca150147c299fd63ae3573202fc4a1e60072c75cb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5






theorem _root_.D1Bound5.two_small_large_C_seventh_power
    (A B S T C D Z : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hT : 0 < T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hZ : 0 < Z) (hCZ : C/2 < Z)
    (hroot : Z^2 ≤ 2*C*D)
    (hform : 1 < 13*B*S^2*T^3/Z+49*S*T^2*Z/(50*A*C^4)) :
    C^7/(10 : ℝ)^50 < D := by sorry

end D1Bound5
end
