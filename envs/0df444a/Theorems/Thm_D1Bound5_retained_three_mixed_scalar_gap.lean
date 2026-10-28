-- Prove2me | Theorems.Thm_D1Bound5_retained_three_mixed_scalar_gap
-- name    : D1Bound5.retained_three_mixed_scalar_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:45.66737+00:00
-- url     : https://prove2.me/theorems/9d056bc9-623f-42fe-b16b-242c2e13681c
-- title:
--   Retained three mixed scalar gap
-- statement:
--   Both retained rows share this scalar implication, including anchors of modulus between one and three. The actual nonzero form and root estimates are inputs; the retained gap is derived.
-- source:
--   D1Bound5/RetainedMixedScalar.lean, lines 5-107, SHA-256 a2dc80a6ed294269b6818161a4e231be3acef13d6a9954e56c9628c66af4bc96. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.retained_three_mixed_scalar_gap
    (A B S T C W Q L lam : ℝ)
    (hA : 1 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S) (hST : S ≤ T)
    (hW : 0 < W) (hQ : 0 < Q) (hQ8 : Q ≤ 8)
    (hlam : 0 < lam) (hlam10 : lam ≤ (1/10 : ℝ))
    (hfront : 2*A*B*S < T)
    (hstrong : B^2*T^3 < (10001/10000 : ℝ)*C)
    (hrootlo : (3999/4000 : ℝ)*T*C < W^2)
    (hroothi : W^2 ≤ T*C+1)
    (hL : 1 ≤ L)
    (hupper : L < 51*(Q*B*S^2)/(100*W) +
      lam*(Q*B*S^2)*W/(A*B*S*T^3)) :
    ((9999/10000 : ℝ)/lam^2) *
      (1/Q-(51051/400000 : ℝ)/(A^2*B^2))^2 *
        (A^2*T^5/S^2) < C := by sorry

end D1Bound5
end
