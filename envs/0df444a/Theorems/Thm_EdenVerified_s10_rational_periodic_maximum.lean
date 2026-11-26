-- Prove2me | Theorems.Thm_EdenVerified_s10_rational_periodic_maximum
-- name    : EdenVerified.s10_rational_periodic_maximum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:24:49.79968+00:00
-- url     : https://prove2.me/theorems/e789e21e-210c-5fb4-bc3b-83390960dc65
-- title:
--   Eden Verified: s10 rational periodic maximum
-- statement:
--   All torus points are periodic maximisers for every positive rational frequency.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L401-L410
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L401-L410

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s10_rational_periodic_maximum (c : ℝ) (hc : 4 < c) (ν : ℚ) (_hν : 0 < ν) :
    torus ⊆ frequencyPeriodicSet c ν ∧
    (∀ p ∈ torus, 0 < 2 * Real.pi * ν.den ∧
      Function.Periodic (fun t : ℝ => frequencyEvolution c ν t p) (2 * Real.pi * ν.den)) ∧
    IsGreatest (frequencyAsymptoticDimension c ν '' frequencyPeriodicSet c ν) (4+4/c) ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (frequencyFiniteTimeDimension c ν t '' frequencyPeriodicSet c ν) (4+4/c)) := by sorry
