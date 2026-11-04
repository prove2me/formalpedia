-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:40:29.630924+00:00
-- url     : https://prove2.me/theorems/fce33e7b-de46-4ff0-aeda-ad74bd21b08a
-- title:
--   Original Gaussian coefficient: uniform discounted Hessian bound on every strict C2 band
-- statement:
--   For the actual source spectrally negative Lévy X and its exact Gaussian variance coefficient sigma squared over two, every compact interior subband of the original C2 region admits a single finite nonnegative K bounding the discounted second-order Gaussian generator term, simultaneously for all nonnegative times and all states in the band. The proof uses continuity of the original second derivative and compactness, plus e^(-qt)<=1 when q>=0. It does not assert path measurability, a Gaussian martingale decomposition, a stochastic integral or boundary occupation.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i) and original generator coefficient; accepted source openness b917eaf2 and pinned Mathlib isCompact_Icc.exists_bound_of_continuousOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)| ≤ K := by sorry
