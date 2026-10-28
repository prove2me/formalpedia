-- Prove2me | Theorems.Thm_D1Bound5_ordinary_height_envelope_from_orders
-- name    : D1Bound5.ordinary_height_envelope_from_orders
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:38.897959+00:00
-- url     : https://prove2.me/theorems/74f62ec9-afc7-45c3-9586-5e52665b7612
-- title:
--   Ordinary height envelope from orders
-- statement:
--   The ordinary height envelope, proved directly from all integer-order inequalities. Its hypotheses expose precisely the analytic input; the full-ring wrapper supplies that input from the actual Bennett matrix.
-- source:
--   D1Bound5/OrdinaryHeightEnvelope.lean, lines 5-91, SHA-256 b7c784fdb6c0b0ae3ce408900a9767c5e55c8d60707a9479b03b7dc8293b12ac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5


theorem _root_.D1Bound5.ordinary_height_envelope_from_orders
    (B C D Z R h r u : ℝ)
    (hB : 1 ≤ B) (hC : 1 < C) (hD : 0 < D) (hZ : 1 ≤ Z) (hR : 0 < R)
    (hprod : C*D < 2*Z^2)
    (hHlog : ordinaryLog10 (42*B^3*C) < ordinaryLog10 C+h)
    (hRlog : 2*ordinaryLog10 C+r < ordinaryLog10 R)
    (hUlog : ordinaryLog10 (253*B^2) < u)
    (hxt : h-r < ordinaryLog10 C) (hx2 : 0 < 2*ordinaryLog10 C+r)
    (horders : ∀ k : ℕ, 1 ≤ k →
      1 < 3*C*(42*B^3*C)^k/(B*Z)+Z/(2*R^k)) :
    ordinaryLog10 D < 7*ordinaryLog10 C+(4*u+8*h-4*r)+
      (2*u*r+(4*u+8*h-4*r)*(h-r))/(ordinaryLog10 C-(h-r))+(2/5 : ℝ) := by sorry

end D1Bound5
end
