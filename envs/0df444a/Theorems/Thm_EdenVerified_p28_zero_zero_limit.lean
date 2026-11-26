-- Prove2me | Theorems.Thm_EdenVerified_p28_zero_zero_limit
-- name    : EdenVerified.p28_zero_zero_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:14.023275+00:00
-- url     : https://prove2.me/theorems/0c7e4a0e-40f7-5c92-aa44-a0d687316efd
-- title:
--   Eden Verified: p28 zero zero limit
-- statement:
--   The zero-zero limiting row has dimension limit zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1369-L1377
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1369-L1377

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p28_zero_zero_limit (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 0)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 0) :
    Tendsto (fun t : ℝ => finiteTimeDimension c t p) atTop (𝓝 0) := by sorry
