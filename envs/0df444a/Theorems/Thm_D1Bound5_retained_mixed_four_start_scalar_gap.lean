-- Prove2me | Theorems.Thm_D1Bound5_retained_mixed_four_start_scalar_gap
-- name    : D1Bound5.retained_mixed_four_start_scalar_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:34.824989+00:00
-- url     : https://prove2.me/theorems/ff1ec2d3-576b-48ee-ae8b-d9c64336ee55
-- title:
--   Retained mixed four start scalar gap
-- statement:
--   Mixed retained-start scalar contradiction: the actual nonzero four-anchor form forces the seventh-power terminal gap. Its assumptions are the concrete form estimate and previously obtained fifth-power growth, not the conclusion.
-- source:
--   D1Bound5/RetainedMixedFourScalar.lean, lines 47-100, SHA-256 a4ae2cd4aa93ee653bdc1acf1660c5bb84963f8e3f72e7896314845810407848. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.retained_mixed_four_start_scalar_gap
    (A B S T C D Z L : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hSC : S ≤ C) (hTC : T ≤ C)
    (hC1000 : 1000 < C) (hZ : 0 < Z)
    (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D)
    (hrootlo : (3999/4000 : ℝ)*C*D < Z^2)
    (hroothi : Z^2 ≤ C*D+1)
    (hL : 1 ≤ L)
    (hupper : L < 13*B*S^2*T^3/Z + (49/50 : ℝ)*S*T^2*Z/(A*C^4)) :
    A^2*C^7/(S^2*T^4) < D := by sorry

end D1Bound5
end
