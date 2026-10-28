-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_scaled_radius_ratio_le
-- name    : D1Bound5.bennett_two_scaled_radius_ratio_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:18.203236+00:00
-- url     : https://prove2.me/theorems/6095ca4c-578e-417c-85f5-1e51b73f5bff
-- title:
--   Bennett two scaled radius ratio le
-- statement:
--   The two possible orders of the local distances give the same rational bound. This keeps the radius choice and the triangle inequality explicit.
-- source:
--   D1Bound5/BennettHeightNormalization.lean, lines 6-38, SHA-256 b5e61e5d6eb88e26d2647369bff77c509498654f629d2229d692762546241a03. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.bennett_two_scaled_radius_ratio_le
    (X δ B r : ℝ) (hX : 0 < X) (hδ : 0 < δ) (hB : 0 < B)
    (hXB : X ≤ B) (hδB : δ ≤ X+B)
    (hr : r = 2*min X δ/5) :
    4*X*δ^2/(r*(X-r)*(δ-r)) ≤ (125/3 : ℝ)*B/X := by sorry



end D1Bound5
end
