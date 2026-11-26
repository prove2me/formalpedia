-- Prove2me | Theorems.Thm_EdenVerified_p29_zero_two_limits
-- name    : EdenVerified.p29_zero_two_limits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:55.217725+00:00
-- url     : https://prove2.me/theorems/908bc19f-343d-466e-8b49-b88ac71291f2
-- title:
--   Eden Verified: p29 zero two limits
-- statement:
--   The first neutral rate tends to zero, the next to minus two, and the dimension
--   to one.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1331-L1344
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1331-L1344

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p29_zero_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧ limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧ limitingSquaredRadius (radiusSq₂ p) = 0)) :
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 0) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 1) atTop (𝓝 (-2)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 1) := by sorry
