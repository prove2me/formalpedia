-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_hjb_to_gaussian_pde
-- name    : AvramDividend.Classical.avram_p4_f11_zero_jump_hjb_to_gaussian_pde
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:39:11.99442+00:00
-- url     : https://prove2.me/theorems/138050c7-6e59-4419-8dab-4407a84e5683
-- title:
--   Original pure-Gaussian HJB drift bound specialises to the exact Gaussian second-order differential inequality
-- statement:
--   If the original spectrally negative Lévy process has zero jump measure and its full generator satisfies the HJB nonpositive drift inequality at every strictly positive reserve below a cap, then the same reserve range satisfies the explicitly Gaussian second-derivative plus deterministic-drift inequality. The original probability space, process, discount rate, barrier and reserve quantifiers are preserved.
-- source:
--   Exact expansion of pinned SpectrallyNegativeLevy.generator under zero jump measure; no surrogate diffusion.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_zero_jump_hjb_to_gaussian_pde
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNu : X.ν = 0)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y - q * w y ≤ 0 := by sorry
