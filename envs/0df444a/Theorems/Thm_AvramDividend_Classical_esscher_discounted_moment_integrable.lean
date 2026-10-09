-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_discounted_moment_integrable
-- name    : AvramDividend.Classical.esscher_discounted_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:49:30.060406+00:00
-- url     : https://prove2.me/theorems/7a0e7450-5e9f-4d4b-a7ba-f22eec20d2af
-- title:
--   Discounted first jump moment integrable from exponential compensator
-- statement:
--   If the BV jump compensator 1-exp(-φz) is integrable for the nonnegative jump-magnitude measure at some φ>0, then z exp(-φz) is also integrable. The pointwise exponential convexity inequality φz exp(-φz)≤1-exp(-φz) gives a norm domination by φ^-1 times the integrable compensator. This removes an independent hypothesis from the root-shifted renewal subcriticality argument.
-- source:
--   Mathlib Real.add_one_le_exp, Integrable.mono; canonical bounded-variation Lévy exponential compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_discounted_moment_integrable
    (ν : Measure ℝ≥0) (φ : ℝ) (hφ : 0 < φ)
    (hJ : Integrable (fun z : ℝ≥0 =>
      1 - Real.exp (-(φ * (z : ℝ)))) ν) :
    Integrable (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ν := by sorry
