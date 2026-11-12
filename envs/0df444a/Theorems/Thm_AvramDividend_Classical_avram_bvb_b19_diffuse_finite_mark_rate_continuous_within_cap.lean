-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
-- name    : AvramDividend.Classical.avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:25:20.017459+00:00
-- url     : https://prove2.me/theorems/73906c68-0012-470b-b23a-10217fbf9f8b
-- title:
--   Diffuse finite-activity negative-mark rate varies continuously with original reserve within finite cap
-- statement:
--   For a finite negative-jump measure with no singleton atoms, the integrated negative-mark value increment is continuous in every initial reserve between zero and finite cap, including the contact points. Diffuseness removes the only post-jump zero-value discontinuity, and Proved phys132 supplies the uniform bound needed for dominated convergence. This is an analytic prerequisite for original phys95 one-sided sample-grid convergence, under Standing plus bounded variation.
-- source:
--   Root-connected phys95 analytic core 912148aa needs continuity of the mark-integrated original signed kernel in reserve, even if w has a discontinuity at negative-mark landing zero. Finite cap and finite activity bound the integral.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (hbC : ENNReal.ofReal b₀ ≤ C) :
    ContinuousWithinAt
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν)
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} b₀ := by sorry
