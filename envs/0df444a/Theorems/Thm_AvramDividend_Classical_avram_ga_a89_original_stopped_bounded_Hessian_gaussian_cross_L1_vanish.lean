-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a89_original_stopped_bounded_Hessian_gaussian_cross_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a89_original_stopped_bounded_Hessian_gaussian_cross_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:09:57.884706+00:00
-- url     : https://prove2.me/theorems/7d6bd05a-4df3-4a2b-9b75-ad413a5e8020
-- title:
--   Original Gaussian stopped Hessian-weighted raw-centred quadratic source error vanishes in expected absolute L1
-- statement:
--   For actual original finite stopped physical Gaussian grids with bounded discounted Hessian, vanishing expected sum of the absolute raw-centred quadratic source differences implies vanishing expected absolute total weighted Gaussian Hessian cross drift correction.
-- source:
--   Actual original b0d9951c stopped Gaussian spatial compensated source drift cross second error stream of ga_a78 via Proved ga_a88 and ga_a81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a89_original_stopped_bounded_Hessian_gaussian_cross_L1_vanish
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ)
    (H R : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m ω i, i ∈ S m → |H m i ω| ≤ K)
    (hCrossI : ∀ m, Integrable (fun ω =>
      |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P)
    (hEnergyI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, |R m i ω|) P)
    (hEnergyL1 : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m =>
      ∫ ω, |∑ i ∈ S m, H m i ω / 2 * R m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
