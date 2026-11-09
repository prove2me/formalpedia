-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_grid_B_nonpositive_ae
-- name    : AvramDividend.Classical.avram_bv_tail12_original_grid_B_nonpositive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:30:39.259409+00:00
-- url     : https://prove2.me/theorems/ac132ab2-3715-473e-8fa9-3d0c7c04abac
-- title:
--   The original BV signed physical-grid B has nonpositive sign almost surely without random generator L1
-- statement:
--   For the original spectrally negative BV Levy process, arbitrary coefficients multiplying the exact raw-removed residual contribute zero almost surely on every physical grid. Pointwise HJB generator sign and nonnegative physical cell widths then make the entire signed B grid nonpositive almost surely. No random-reserve GeneratorIntegrable-to-L1 inference, uniform envelope K, or expectation of B is assumed. Substitution of the canonical cofinal-band good indicator, left-limit reserve Z and derivative weight A recovers the exact B sign relevant to 0b2da5b3 and the corrected BV finite-horizon signed budget.
-- source:
--   AVRAM BV-TAIL12, 8 November 2026. Exact source 6d8e04eb and the original pointwise HJB hypotheses; conditional bridge to BV-CORRECT12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_weighted_grid_residual_zero_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_original_grid_B_nonpositive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → Ω → ℕ → ℝ) (good : ℕ → Ω → ℕ → Prop)
    (hgood : ∀ n ω i, good n ω i →
      0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C)
    (A : ℕ → Ω → ℕ → ℝ) (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω =
      (∑ i ∈ Finset.range (n + 1),
        if good n ω i then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n ω i) - q * w (Z n ω i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         A n ω i * (R (u n i) - R (u n (i + 1))))) :
    ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by sorry
