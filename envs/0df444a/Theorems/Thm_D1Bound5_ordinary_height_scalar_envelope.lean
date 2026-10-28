-- Prove2me | Theorems.Thm_D1Bound5_ordinary_height_scalar_envelope
-- name    : D1Bound5.ordinary_height_scalar_envelope
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:30:53.238074+00:00
-- url     : https://prove2.me/theorems/b1d3bdcd-59c5-4606-85fe-32b0f51c6631
-- title:
--   Ordinary height scalar envelope
-- statement:
--   The exact rational-parameter algebra of the ordinary height envelope. Here x,z,d are base-ten logarithms and p,q are the residual rate and coefficient-height logarithms.
-- source:
--   D1Bound5/OrdinaryHeightScalar.lean, lines 56-87, SHA-256 0823b901aedbcca1a333b2b988ab8e6173c80406182e7af0372435df321e588d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5




theorem _root_.D1Bound5.ordinary_height_scalar_envelope (x z d p q h r u : ℝ)
    (hz : 0 ≤ z) (hq : 0 ≤ q)
    (hp : 2*x+r < p) (hp0 : 0 < 2*x+r)
    (hqh : q < x+h) (hxt : h-r < x)
    (hbound : z*(p-q) < (2*x+u)*p)
    (hd : d < (2/5 : ℝ)-x+2*z) :
    d < 7*x+(4*u+8*h-4*r)+
      (2*u*r+(4*u+8*h-4*r)*(h-r))/(x-(h-r))+(2/5 : ℝ) := by sorry



end D1Bound5
end
