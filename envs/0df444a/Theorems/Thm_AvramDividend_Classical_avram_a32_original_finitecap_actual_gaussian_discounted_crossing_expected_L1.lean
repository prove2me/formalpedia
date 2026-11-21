-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
-- name    : AvramDividend.Classical.avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:34:18.567173+00:00
-- url     : https://prove2.me/theorems/ebbc8b9e-9982-42bd-b49f-cbf6da8ed42c
-- title:
--   Actual finitecap original Gaussian physical crossing expected positive error vanishes under stopped discounted weights
-- statement:
--   Under the true original Gaussian Lévy process, actual bounded random physical crossing clocks and positive compact stopped reserve band, the expected discounted positive spatial crossing error tends to zero for measurable weights 0≤E_m≤1. All integrability, pathwise convergence and uniform domination are derived from original X: proved a31 per-mesh positive error integrability, a29 unweighted crossing expected limit and a30 positive-weighted L1 squeeze. No independent martingale or assumed spatial error budget. Original discount exp(-qρ) fits the weight bounds; ruin and all full cells remain separate.
-- source:
--   Exact original ν=0 physical finitecap caplinear Gaussian discounted crossing L1 source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P)    (E : ℕ → Ω → ℝ)
    (hEm : ∀ m, AEStronglyMeasurable (E m) P)
    (hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1) :
    Tendsto (fun m => ∫ ω,
      E m ω * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by sorry
