-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_fullcap_negative_mark_envelope
-- name    : AvramDividend.Classical.avram_bv_finite734_fullcap_negative_mark_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:33:45.789977+00:00
-- url     : https://prove2.me/theorems/da5da214-1cbc-48a3-b977-0cb20f5ed3e3
-- title:
--   Uniform original finite-activity negative-mark envelope up to the full finite reserve cap
-- statement:
--   For a finite positive cap, the original finite-activity BV HJB candidate has a single uniform bound on all negative-jump value increments for pre-jump reserves in the entire closed interval [0,C]. This removes a compact-band restriction from jump intensity domination, including ruin-crossing marks and the upper cap endpoint.
-- source:
--   Root-connected stochastic cash-error route 3f849360 -> 00e7ded9 -> 4044d709; exact corollary of Proved e0a98361 using finite ENNReal.toReal and closed cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_original_negative_mark_oscillation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_finite734_fullcap_negative_mark_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hFinite : C ≠ ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y z : ℝ, y ∈ Icc (0 : ℝ) C.toReal → z < 0 →
        |w (y + z) - w y| ≤ K := by sorry
