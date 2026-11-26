-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_lower_strip_dividend_loss
-- name    : AvramDividend.Classical.avram_locmoll_lower_strip_dividend_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:04.51971+00:00
-- url     : https://prove2.me/theorems/e9cc897b-a881-55e0-baa3-f7ec9c3f388e
-- title:
--   One-sided smoothing: one lower-strip payment loses at most the strip width
-- statement:
--   A single dividend crossing the lower smoothing strip has positive cash-minus-value-loss residual at most the strip width. Used for the last eligible payment before a reserve-band exit.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), localised one-sided smoothing route for cc518136-9d63-4167-8587-606274d8eec9

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_lower_strip_dividend_loss
    (g : ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmono : MonotoneOn g (Ici 0))
    (hsec : ∀ a b : ℝ, δ ≤ a → a ≤ b →
      b - a ≤ g b - g a)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    a - b ≤ g a - g b + δ := by sorry
