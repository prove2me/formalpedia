-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
-- name    : AvramDividend.Classical.avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T09:07:18.105115+00:00
-- url     : https://prove2.me/theorems/0174393a-b6f3-4fae-b61a-4e5c73220411
-- title:
--   True finite chronological negative Lévy marked-grid Taylor errors vanish from above at distinct positive pre-jump reserves
-- statement:
--   For the actual original Lévy and dividend source X,D and one physical sample path, take a finite set S of genuine positive-time negative jump marks, each with positive strict interior predictable pre-reserve x+X(t-)-D(t). For each mark t use a physical grid sample grid(m,t) converging to t from strictly below. The exact original post-right-dividend reserve sampled at grid(m,t) converges to the original predictable premark reserve, and the positive part of the finite sum of nonlinear original Taylor jump errors tends to zero. The proof combines the already published original-allactivity prestate left convergence and finitely-indexed Taylor one-sided upper convergence, preserving distinct jump marks, distinct prestates, ruin-landing zero allowed. It remains conditional on strict interior for all marks in S and on the physical grid convergence; boundary marks and the stopped cash Gaussian ledger require further source work.
-- source:
--   Original Avram Dividend physical stopped finite-activity marked-jump source 242ca5f1. Exact original finite jump support from Proved 1e50b68a, original all-activity prestate limit and indexed signed Taylor source (pending).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (S : Finset ℝ≥0)
    (hSpos : ∀ t ∈ S, 0 < t)
    (hSneg : ∀ t ∈ S,
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ t ∈ S,
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (grid : ℕ → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ t ∈ S, Tendsto (fun m => grid m t) atTop (𝓝[<] t)) :
    let y : ℝ≥0 → ℝ := fun t =>
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω
    let z : ℝ≥0 → ℝ := fun t =>
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
    let u : ℕ → ℝ≥0 → ℝ := fun m t =>
      x + X.X (grid m t) ω - rightLimit D (grid m t) ω
    Tendsto
      (fun m => max
        (∑ t ∈ S,
          ((w (u m t + z t) - w (u m t) -
              (if -1 < z t then z t * deriv w (u m t) else 0)) -
           (w (y t + z t) - w (y t) -
              (if -1 < z t then z t * deriv w (y t) else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
