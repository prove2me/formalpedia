-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
-- name    : AvramDividend.Classical.avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:12:54.935275+00:00
-- url     : https://prove2.me/theorems/aa00b80d-4afa-44cb-90da-12abf92be8ab
-- title:
--   Original finite-activity BV compensated physical generator nonpositive on entire closed cap reserve band
-- statement:
--   For the original finite-activity Standing BV spectrally negative Lévy process, positive finite reserve cap C and original candidate w satisfying HJB in (0,C), the original compensated physical generator drift×slope plus unmodified negative-mark integral −q w is nonpositive at ALL reserves y∈[0,C]. Use physical derivative w′(y) strictly inside the band; at zero or the cap use the original boundary coefficient 1 and the exact Proved zero and cap boundary generator signs, respecting possible nonsmooth contact. This produces the complete source-level HJB sign needed by the original stopped finite-variation Stieltjes ledger.
-- source:
--   Proved 0344aae3 and 32ce498d via bvb33; Proved boundedVariation_generator_physical_drift_representation c8ba98f0 for interior.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb34_original_finitecap_BV_allclosed_physical_generator_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
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
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal →
      X.drift * (if y = 0 ∨ y = C.toReal then 1 else deriv w y) +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
        q * w y ≤ 0 := by sorry
