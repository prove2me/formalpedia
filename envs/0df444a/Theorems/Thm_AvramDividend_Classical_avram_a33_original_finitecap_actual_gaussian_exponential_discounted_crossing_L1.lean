-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a33_original_finitecap_actual_gaussian_exponential_discounted_crossing_L1
-- name    : AvramDividend.Classical.avram_a33_original_finitecap_actual_gaussian_exponential_discounted_crossing_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:36:31.301778+00:00
-- url     : https://prove2.me/theorems/090e6803-93f3-4966-b50e-594e68b76127
-- title:
--   Actual stopped original finitecap Gaussian caplinear spatial crossing error vanishes with exact exponential discount
-- statement:
--   The original ν=0 spectrally negative Gaussian Lévy process with true random mesh clocks, a physical postpayment reserve in a compact positive band below the finite cap, and measurable stopped discount times ρ_m has vanishing expected positive caplinear spatial crossing error weighted by the exact factor exp(-qρ_m), q≥0. Prove by deriving the measurable weights and 0≤exp(-qρ)≤1 from actual stopping clocks, and using the a32 original discounted positive crossing theorem. Uses X.isProbability, no artificial martingale or extra finite-measure assumption; still localised pre-ruin and separate from full-cell drift and dividend cash.
-- source:
--   Actual original stopped q-discounted finitecap Gaussian physical positive spatial crossing L1 source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a33_original_finitecap_actual_gaussian_exponential_discounted_crossing_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
       w (y m ω)) 0) P)    (q : ℝ) (hq : 0 ≤ q)
    (ρ : ℕ → Ω → ℝ≥0) (hρmeas : ∀ m, Measurable (ρ m)) :
    Tendsto (fun m => ∫ ω,
      Real.exp (-(q * (ρ m ω : ℝ))) * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by sorry
