-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
-- name    : AvramDividend.Classical.avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:23:36.900514+00:00
-- url     : https://prove2.me/theorems/6dc655d0-8672-499b-99a3-ebd5f71bf99d
-- title:
--   Literal original stopped physical-grid signed payment residual equals the negative of true prepayment potential drop sum
-- statement:
--   For the exact original spectrally negative Levy X and its right-limit dividend D, the literal canonical physical-grid payment residual sum with postpayment-minus-prepayment w differences equals the negative discounted sum of the corresponding prepayment-minus-postpayment differences, retaining the identical initial right-dividend potential correction. Pure signed finite-sum algebra specialized to the original stopped physical grid, needed to close the original topcap strict eventwise cash inequality from the separately Proved per-grid source Stieltjes bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_weighted_signed_potential_drop_sum_swap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let E : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ)))
    let Y : ℝ≥0 → ℝ := fun r => x + X.X r ω - rightLimit D r ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (w (x - rightLimit D 0 ω) - w x) -
      (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (w (Z i) - w (Y (v (i + 1))))) := by sorry
