-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB52_original_barrier_masked_physical_noise_sum_eq_first_order
-- name    : AvramDividend.Classical.avram_gbB52_original_barrier_masked_physical_noise_sum_eq_first_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:25:46.171399+00:00
-- url     : https://prove2.me/theorems/72053d65-5ff9-44fc-93d8-955230a9fc04
-- title:
--   Actual original capped Gaussian physical-grid martingale sum is purely first-order on the upper-strip tube
-- statement:
--   For the original x=C=1/8 cap barrier, the exact source prepayment state Y_i is above the j=9 threshold b=5/44 throughout a source tube of radius 1/400. Thus for every finite grid, with any physical times s_i, centred increments Z_i, discount q and Hessian-variance factor v, the original stopped physical-grid source G_i Z_i + H_i (Z_i²-v) is exactly the masked discounted first-order sum. This is a finite-grid pathwise identity, retaining the source's rightLimit D and left-start stopping mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_barrier_postpayment_rightLimit_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB52_original_barrier_masked_physical_noise_sum_eq_first_order
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z : ℕ → ℝ)
    (q a v : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
       else 0) * Z i +
      (if s i < T then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ)
         then iteratedDeriv 2 w (Y i) else 0)
       else 0) * (Z i ^ 2 - v)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by sorry
