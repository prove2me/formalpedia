-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
-- name    : AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:34:04.072481+00:00
-- url     : https://prove2.me/theorems/b1b691b1-775b-4e7e-908f-ecf04e358f12
-- title:
--   Original UBV zero-jump compact discounted C² bounds with automatically open cap-interior domain
-- statement:
--   For the original zero-jump unbounded-variation spectrally negative Levy process, the exact discounted gradient and Hessian are jointly bounded on every compact interior band uniformly in nonnegative time. The open-set condition is discharged automatically for every ENNReal cap using an independently Proved original interior openness theorem. Consequently the source bound matches the actual a029846e positive-clock proof hypotheses without extra positivity or topology assumptions.
-- source:
--   Direct source-exact original capped Gaussian localisation; Proved cf422b36 and b917eaf2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_autoopen_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH) := by sorry
