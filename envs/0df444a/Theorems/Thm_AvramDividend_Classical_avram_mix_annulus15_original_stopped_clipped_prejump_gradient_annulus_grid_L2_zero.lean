-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
-- name    : AvramDividend.Classical.avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:06:42.205335+00:00
-- url     : https://prove2.me/theorems/60e2e6e0-e234-40cf-8279-41662003d94a
-- title:
--   Original stopped clipped pre-jump discounted derivative annulus physical-grid L2 and mean-zero
-- statement:
--   Original actual discounted clipped pre-jump controlled reserve derivative yields a stopped centred L2 compensated negative-annulus finite-grid martingale. Directly subtract two Proved source-specific original full-cutoff stopped martingales using original finite physical chronological count-additivity and Levy rate additivity, preserving all actual X,D,τ and filtration.
-- source:
--   Same-source gradient annulus martingale from Proved a484cc37 at two cutoffs, Proved 836786f5 original chronological count additivity and Proved 832d1bcb original Levy rate; independent of any pending generic theorem; feeds 5f12c023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_clipped_prejump_gradient_full_cutoff_L2_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_real_window_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_original_stopped_clipped_prejump_gradient_annulus_grid_L2_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cutLo cutHi : ℕ) (hCut : cutLo ≤ cutHi)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (n : ℕ) :
    let B : Set ℝ := Ioc (-(1 / ((cutLo : ℝ) + 1)))
      (-(1 / ((cutHi : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B)
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
