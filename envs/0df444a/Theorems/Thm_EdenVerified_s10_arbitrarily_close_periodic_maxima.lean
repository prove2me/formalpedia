-- Prove2me | Theorems.Thm_EdenVerified_s10_arbitrarily_close_periodic_maxima
-- name    : EdenVerified.s10_arbitrarily_close_periodic_maxima
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:24:52.481567+00:00
-- url     : https://prove2.me/theorems/1b4b9ab7-2d5a-5dbd-bd46-f641c3893d38
-- title:
--   Eden Verified: s10 arbitrarily close periodic maxima
-- statement:
--   Positive rational frequencies with periodic maxima approach sqrt(2) arbitrarily
--   closely.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L414-L419
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L414-L419

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s10_arbitrarily_close_periodic_maxima (c : ℝ) (hc : 4 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : ℚ, 0 < ν ∧ |(ν : ℝ)-Real.sqrt 2| < ε ∧
      IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
      ∀ t : ℝ, 0 < t →
        IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c) := by sorry
