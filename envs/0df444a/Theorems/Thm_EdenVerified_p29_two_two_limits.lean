-- Prove2me | Theorems.Thm_EdenVerified_p29_two_two_limits
-- name    : EdenVerified.p29_two_two_limits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:59.560133+00:00
-- url     : https://prove2.me/theorems/b90e4596-845f-4a39-91e9-caa2cfe30cb1
-- title:
--   Eden Verified: p29 two two limits
-- statement:
--   Both neutral rates tend to zero, the next to minus four, and the dimension to
--   two.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1348-L1366
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1348-L1366

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p29_two_two_limits (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2) :
    (∀ i : Fin 5, i.val < 2 →
      Tendsto (fun t : ℝ => normalizedLogSingularValues c t p i) atTop (𝓝 0)) ∧
    Tendsto (fun t : ℝ => normalizedLogSingularValues c t p 2) atTop (𝓝 (-4)) ∧
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 2) := by sorry
