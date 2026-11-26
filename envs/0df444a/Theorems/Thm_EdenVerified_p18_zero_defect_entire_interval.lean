-- Prove2me | Theorems.Thm_EdenVerified_p18_zero_defect_entire_interval
-- name    : EdenVerified.p18_zero_defect_entire_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:52:36.994147+00:00
-- url     : https://prove2.me/theorems/f987d981-604c-453c-bf49-42fa2b9b1738
-- title:
--   Eden Verified: p18 zero defect entire interval
-- statement:
--   The defect vanishes exactly when both radii remain unit throughout the interval.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1839-L1850
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1839-L1850

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p18_zero_defect_entire_interval (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    volumeDefect t p = 0 ↔ ∀ τ ∈ Icc (0 : ℝ) t,
      radiusSq₁ (evolution c τ p) = 1 ∧ radiusSq₂ (evolution c τ p) = 1 := by sorry
