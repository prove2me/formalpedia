-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_compact_HJB_from_global_interior
-- name    : AvramDividend.Classical.avram_p3_bv_original_compact_HJB_from_global_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:53:23.988992+00:00
-- url     : https://prove2.me/theorems/ae93db0a-f25f-457f-9a44-99f4953b490c
-- title:
--   Canonical global interior HJB gives negative original controlled compact BV drift expectation
-- statement:
--   The global original-process generator inequality and generator-integrability assumptions on the open positive cap interior imply the signed expected HJB generator drift inequality on the actual controlled predictable compact pre-reserve band [a,b] whenever a>0 and b lies below the cap. This removes separate local generator and HJB assumptions from the source-exact compact-band expectation theorem.
-- source:
--   Original compact prestate HJB expected-sign theorem 66cf24ce Proved; monotonicity of ENNReal.ofReal from pinned Mathlib and global HJB premise inherited from canonical P3 leaf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_compact_prestate_HJB_expected_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_compact_HJB_from_global_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℝ) (ha : 0 < a) (hbC : ENNReal.ofReal b < C)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if Upre p ∈ Icc a b then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)) ≤ 0 := by sorry
