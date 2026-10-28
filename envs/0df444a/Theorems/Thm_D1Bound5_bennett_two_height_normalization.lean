-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_height_normalization
-- name    : D1Bound5.bennett_two_height_normalization
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:44:54.779533+00:00
-- url     : https://prove2.me/theorems/57ba8da6-ec72-4ad0-96af-5545ca55288c
-- title:
--   Bennett two height normalization
-- statement:
--   The exact local coefficient majorant, after multiplication by the integral clearing factor, has exponential base strictly below 42. All geometric and scale hypotheses are elementary real inequalities; no bound on the coefficient being estimated occurs among the assumptions.
-- source:
--   D1Bound5/BennettHeightNormalization.lean, lines 40-147, SHA-256 b5e61e5d6eb88e26d2647369bff77c509498654f629d2229d692762546241a03. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.bennett_two_height_normalization
    (X Y δ B C N U r : ℝ) (k : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ)
    (hB : 0 < B) (hC : 0 < C) (hXB : X ≤ B)
    (hδB : δ ≤ X+B) (hN : N = X*Y*C)
    (hscale : 1000 ≤ N/B) (hUlo : N-X ≤ U) (hUhi : U ≤ N+X)
    (hradius : r = 2*min X δ/5) (hk : 1 ≤ k) :
    (4*X*Y*δ^2)^k * ((U+r)/U) *
        ((U+r)/(r*(X-r)*(δ-r)))^k < (42*Y^2*B*C)^k := by sorry

end D1Bound5
end
