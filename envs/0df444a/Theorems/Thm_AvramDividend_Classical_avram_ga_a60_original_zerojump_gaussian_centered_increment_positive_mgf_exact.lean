-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
-- name    : AvramDividend.Classical.avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:21:01.04157+00:00
-- url     : https://prove2.me/theorems/e52edd63-233e-4223-a10d-defdd6d4bbfa
-- title:
--   Original no-jump Levy Gaussian centred physical increment has exact positive exponential moment
-- statement:
--   On the genuine original Gaussian Levy source and right-continuous filtration, every deterministic drift-centred source increment divided by nonzero volatility has a positive-parameter exponential moment exactly equal to the Gaussian moment exp(dt theta squared over two).
-- source:
--   Direct original no-jump Gaussian positive only large upper-spatial-tail control in b0d9951c with ga_a49 Chernoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a60_original_zerojump_gaussian_centered_increment_positive_mgf_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * (((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) ∂P) =
    Real.exp (((t - s : ℝ≥0) : ℝ) * θ^2 / 2) := by sorry
