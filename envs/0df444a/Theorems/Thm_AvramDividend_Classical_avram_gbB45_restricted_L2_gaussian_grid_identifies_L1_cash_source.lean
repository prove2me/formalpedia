-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB45_restricted_L2_gaussian_grid_identifies_L1_cash_source
-- name    : AvramDividend.Classical.avram_gbB45_restricted_L2_gaussian_grid_identifies_L1_cash_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:01:42.050283+00:00
-- url     : https://prove2.me/theorems/0fd7a285-9a00-422c-9ac7-04e847f6c1d9
-- title:
--   Original Gaussian physical-grid L1 source coincides with explicit L2 limit on stopped event
-- statement:
--   If a physical Gaussian mesh source M converges in restricted L1 to the original martingale limit N and globally in L2 to the proposed Brownian integral J, then N=J almost everywhere on the chosen stopping event. This source-identification bridge applies the two existing Proved restricted L1 uniqueness and L2-to-L1 transfer results and leaves actual mesh L2 convergence explicit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_restricted_real_L1_two_limits_unique_ae
import Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB45_restricted_L2_gaussian_grid_identifies_L1_cash_source
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (M : ℕ → Ω → ℝ) (N J : Ω → ℝ)
    (hNI : Integrable N (P.restrict A))
    (hJI : Integrable J (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hMLp : ∀ m, MemLp (M m) 2 P) (hJLp : MemLp J 2 P)
    (hL2 : Tendsto (fun m : ℕ => eLpNorm (M m - J) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ᵐ ω ∂(P.restrict A), N ω = J ω := by sorry
