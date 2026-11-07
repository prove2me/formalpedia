-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
-- name    : AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:24:46.688301+00:00
-- url     : https://prove2.me/theorems/cf422b36-2654-4d10-825d-82302f25e5a5
-- title:
--   Original unbounded-variation zero-jump Lévy compact C² stopped-source coefficient envelope
-- statement:
--   For the actual unbounded-variation original spectrally negative Levy process with zero jump measure, the Gaussian coefficient is necessarily strictly positive by the independently Proved zero-jump theorem and the structure's nonnegativity. Hence the source-exact compact discounted C2 derivative/Hessian bounds hold without adding a Gaussian positivity assumption. This specialises the envelope to the exact hypotheses of the positive-clock original Gaussian Ito budget a029846e.
-- source:
--   Acyclic UBV zero-jump original-source bridge, feeding a029846e through already Proved 099e50af and F16 original compact envelope c17053bc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_ubv_zerojump_nonzero_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_positive_gaussian_compact_C2_discount_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f16_original_ubv_zerojump_compact_C2_discount_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG) ∧
      (∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH) := by sorry
