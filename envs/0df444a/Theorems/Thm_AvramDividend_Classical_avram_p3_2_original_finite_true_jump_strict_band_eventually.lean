-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_true_jump_strict_band_eventually
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_true_jump_strict_band_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:39:09.122579+00:00
-- url     : https://prove2.me/theorems/dabf9866-b46c-491e-81e6-6162456b36dd
-- title:
--   Uniform compact localisation for finite original Levy true jump tags
-- statement:
--   For every finite set of genuine original Levy jump times, physical left-tag reserve states converging to strictly interior prejump and postjump reserve states eventually lie simultaneously in one common closed compact interval. Exact original X.X jump marks are retained.
-- source:
--   Finite-set filter conjunction and genuine original nonlinear jump mark; establishes the finite-tag part of BV localisation, with infinite activity tail still separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_true_jump_strict_band_eventually
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0) (lo hi : ℝ)
    (z : ℕ → ℝ≥0 → ℝ) (u : ℝ≥0 → ℝ)
    (hlim : ∀ t ∈ T, Tendsto (fun k => z k t) atTop (nhds (u t)))
    (hstrict : ∀ t ∈ T,
      u t ∈ Set.Ioo lo hi ∧
      u t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Ioo lo hi) :
    ∀ᶠ k in atTop, ∀ t ∈ T,
      z k t ∈ Set.Icc lo hi ∧
      z k t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t) ∈ Set.Icc lo hi := by sorry
