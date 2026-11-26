-- Prove2me | Theorems.Thm_EdenVerified_p28_unit_unit_limit
-- name    : EdenVerified.p28_unit_unit_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:25.056822+00:00
-- url     : https://prove2.me/theorems/5db5f55b-6d4b-4377-ba01-06b1dae355b3
-- title:
--   Eden Verified: p28 unit unit limit
-- statement:
--   The unit-unit limiting row has dimension limit four plus four over c.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1380-L1389
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1380-L1389

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_unit_unit_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 (4+4/c)) := by sorry
