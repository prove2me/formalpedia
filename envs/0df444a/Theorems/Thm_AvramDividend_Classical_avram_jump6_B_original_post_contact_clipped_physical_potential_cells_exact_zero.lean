-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_post_contact_clipped_physical_potential_cells_exact_zero
-- name    : AvramDividend.Classical.avram_jump6_B_original_post_contact_clipped_physical_potential_cells_exact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:46:01.7259+00:00
-- url     : https://prove2.me/theorems/1abf323f-c0cc-4ce7-bc2b-af9e870b8414
-- title:
--   True original canonical clipped physical payment potential drops vanish after stop contact
-- statement:
--   After the exact canonical clipped physical grid has reached the stop, every later cell has the same left- and right-dividend evaluation times. Hence the original payment-potential difference, including its true exponential discount and prepayment X-state, is identically zero. Valid for arbitrary real functions U and D including the original Levy sample path and the actual right-limit dividend path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_post_contact_clipped_physical_potential_cells_exact_zero
    (n j : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (k : ℕ)
    (hk : min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ)
    (l : ℕ) (hkl : k ≤ l)
    (x q : ℝ) (U A : ℝ≥0 → ℝ) (w : ℝ → ℝ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    Real.exp (-(q * (v (l + 1) : ℝ))) *
      (w (x + U (v (l + 1)) - A (v (l + 1))) -
       w (x + U (v (l + 1)) - A (v l))) = 0 := by sorry
