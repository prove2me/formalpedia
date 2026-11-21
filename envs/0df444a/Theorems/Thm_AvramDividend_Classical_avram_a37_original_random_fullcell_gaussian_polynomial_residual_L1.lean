-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a37_original_random_fullcell_gaussian_polynomial_residual_L1
-- name    : AvramDividend.Classical.avram_a37_original_random_fullcell_gaussian_polynomial_residual_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:26:17.188724+00:00
-- url     : https://prove2.me/theorems/21bc9df9-396f-4299-ad0c-3d7e7369a41e
-- title:
--   Actual random full Gaussian grid cell polynomial Taylor residual vanishes in L1
-- statement:
--   For original zerojump Gaussian spectrally negative Lévy X, arbitrary random canonical physical grid index i_m with full cell inside bounded horizon n and actual centred Gaussian increment Z_m=X(s+Δ)-X(s)-Δc, any measurable cell residual H_m bounded pointwise by K(|Z_m|+Z_m²+Δ) has E|H_m|→0. Use Proved a117 original random fullcell increment→0, Proved a400 centred Gaussian bounded-horizon square-integrable supremum, and Proved a127 generic polynomial residual dominated convergence. This handles true original physical full-cell compensated Taylor remainders with random crossing index, avoiding artificial independent noise and leaving only the derivation of the concrete Taylor bound on the actual stopped HJB coefficients.
-- source:
--   Original zerojump actual Gaussian physical fullcell compensated polynomial remainder expected-L1, random mesh crossing indices.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a37_original_random_fullcell_gaussian_polynomial_residual_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ + Δ ≤ (n : ℝ≥0))
    (Z : ℕ → Ω → ℝ)
    (hZeq : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      Z m ω = X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)
    (K : ℝ) (hK : 0 ≤ K) (H : ℕ → Ω → ℝ)
    (hError : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      |H m ω| ≤ K * (|Z m ω| + (Z m ω)^2 + (Δ : ℝ)))
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => |H m ω|) P) :
    Tendsto (fun m => ∫ ω, |H m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
