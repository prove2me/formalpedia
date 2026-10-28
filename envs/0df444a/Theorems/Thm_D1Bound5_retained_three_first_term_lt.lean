-- Prove2me | Theorems.Thm_D1Bound5_retained_three_first_term_lt
-- name    : D1Bound5.retained_three_first_term_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:08.929648+00:00
-- url     : https://prove2.me/theorems/e75ea1a0-8324-4d8a-9333-b3ec542124cf
-- title:
--   Retained three first term lt
-- statement:
--   Exact scalar control of the first summand in the retained three-anchor form. This combines the proved strong two-anchor gap with the terminal-root lower bound, retaining the normalized Vandermonde parameter.
-- source:
--   D1Bound5/RetainedGapScalar.lean, lines 11-52, SHA-256 eaf49f8f7c6b30d9a009d68ad6e151008415007d3e910e0adf243de47b84ad81. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.retained_three_first_term_lt
    (A B S T C W Q : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 < S)
    (hW : 0 < W) (hQ : 0 < Q)
    (hfront : 2*A*B*S < T)
    (hstrong : B^2*T^3 < (10001/10000 : ℝ)*C)
    (hroot : (3999/4000 : ℝ)*T*C < W^2) :
    51*(Q*B*S^2)/(100*W) < (51051/400000 : ℝ)*Q/(A^2*B^2) := by sorry



end D1Bound5
end
