-- Prove2me | Theorems.Thm_D1Bound5_retained_three_h48_scalar_gap
-- name    : D1Bound5.retained_three_h48_scalar_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:15.954511+00:00
-- url     : https://prove2.me/theorems/6dcda610-92d0-4b5b-932c-00b216bfa70c
-- title:
--   Retained three h48 scalar gap
-- statement:
--   The H48 retained gap follows from the actual nonzero three-anchor form estimate and the two terminal-root norm inequalities. No retained-gap inequality or coarse growth conclusion is supplied as a hypothesis.
-- source:
--   D1Bound5/RetainedGapScalar.lean, lines 54-151, SHA-256 eaf49f8f7c6b30d9a009d68ad6e151008415007d3e910e0adf243de47b84ad81. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.retained_three_h48_scalar_gap
    (A B S T C W Q L : ℝ)
    (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S) (hST : S ≤ T)
    (hW : 0 < W) (hQ : 0 < Q) (hQ8 : Q ≤ 8)
    (hfront : 2*A*B*S < T)
    (hstrong : B^2*T^3 < (10001/10000 : ℝ)*C)
    (hrootlo : (3999/4000 : ℝ)*T*C < W^2)
    (hroothi : W^2 ≤ T*C+1)
    (hL : 1 ≤ L)
    (hupper : L < 51*(Q*B*S^2)/(100*W) +
      (19/200 : ℝ)*(Q*B*S^2)*W/(A*B*S*T^3)) :
    ((9999/10000 : ℝ)*(200/19)^2) *
      (1/Q-(51051/400000 : ℝ)/(A^2*B^2))^2 *
        (A^2*T^5/S^2) < C := by sorry

end D1Bound5
end
