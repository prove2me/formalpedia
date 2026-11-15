-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
-- name    : AvramDividend.Classical.avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:12:01.26869+00:00
-- url     : https://prove2.me/theorems/e317bc40-8995-4d1b-8faa-487b2212c4d5
-- title:
--   Original finite-activity BV generator compensated nonpositivity at both zero and finite-cap boundary
-- statement:
--   For an original Standing BV spectrally negative Lévy process with finite negative-jump intensity, smooth positive-reserve HJB candidate w, strictly positive finite cap C, preserve original physical drift and actual Lévy negative-mark compensator ν. Prove the closed generator drift + ∫[w(y+z)-w(y)]ν(dz) − q w(y)≤0 at BOTH boundary points y=0 and y=C, by combining independently Proved original zero-reserve HJB 0344aae3 and the now Proved/public closed-cap HJB 32ce498d. This supplies a single boundary source premise for stopped Stieltjes analysis of interior and boundary contact.
-- source:
--   Public Proved 0344aae3 and 32ce498d, original mixed-reserve BV-B Stieltjes interface.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb33_original_finitecap_BV_full_boundary_generator_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, y = 0 ∨ y = C.toReal →
      X.drift +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
        q * w y ≤ 0 := by sorry
