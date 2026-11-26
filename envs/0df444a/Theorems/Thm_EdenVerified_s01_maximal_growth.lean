-- Prove2me | Theorems.Thm_EdenVerified_s01_maximal_growth
-- name    : EdenVerified.s01_maximal_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:21:24.09382+00:00
-- url     : https://prove2.me/theorems/2f5808dc-0c4b-4529-901d-cce8fe7366ce
-- title:
--   Eden Verified: s01 maximal growth
-- statement:
--   Maxima are attained over both unit and nonzero exterior vectors.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L139-L144
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L139-L144

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s01_maximal_growth (c : ℝ) (p : PhaseSpace) (k : ℕ) (hk : k ≤ 5) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) ∧
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) := by sorry
