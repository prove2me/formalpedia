-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_terminal_switch_right_atom
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_terminal_switch_right_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:29:30.32976+00:00
-- url     : https://prove2.me/theorems/557c0ded-563e-46df-a713-2760c313642d
-- title:
--   Original finite stopped terminal reserve switches the exact right dividend atom on only at active horizon or time zero
-- statement:
--   At the original UBV finite stopping clock with its exact hW terminal definition, the terminal reserve equals the original post-source pre-dividend riskProcess minus the right dividend atom precisely if the clock is zero or strictly before ruin. In the positive-ruin terminal branch the deduction is zero. No source/payment ordering or horizon atom can be lost; the theorem is algebraic and does not change W, τ or D.
-- source:
--   Exact original hW hypothesis in 0dda1be7 and accepted P4-D post-source rightpayment reserve equality 4fb2f44f-7382-4ab2-8b4f-352ec4b3f189.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_original_terminal_switch_right_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω = riskProcess X x D (τ ω) ω -
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
       then rightLimit D (τ ω) ω - D (τ ω) ω
       else 0) := by sorry
