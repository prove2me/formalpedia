-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
-- name    : AvramDividend.Classical.avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:29:26.474082+00:00
-- url     : https://prove2.me/theorems/47f187ca-f87e-44e7-bf92-b54423097089
-- title:
--   Exponential control consumption dominates exact discounted continuous and right-atomic dividend increments
-- statement:
--   For nondecreasing cumulative payment a≤b and θ≥0, the consumed exponential discount exp(-θa)−exp(-θb) is at least θ exp(-θb)(b−a). This is the exact finite-cell inequality needed to compare the already-Proved original Lévy martingale consumption with Stieltjes dividend mass, covering diffuse and atomic portions simultaneously; follows from 1+z≤exp z.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and positivity of exp, with exact algebra

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
    (θ a b : ℝ) (hθ : 0 ≤ θ) (hab : a ≤ b) :
    θ * Real.exp (-(θ * b)) * (b - a) ≤
      Real.exp (-(θ * a)) - Real.exp (-(θ * b)) := by sorry
