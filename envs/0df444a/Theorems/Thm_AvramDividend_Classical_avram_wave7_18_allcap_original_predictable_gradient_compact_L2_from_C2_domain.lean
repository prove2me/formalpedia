-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain
-- name    : AvramDividend.Classical.avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:18:58.422046+00:00
-- url     : https://prove2.me/theorems/8a71fa31-67f1-4fb8-8d4c-ba873ffbe716
-- title:
--   All-cap original predictable reserve gradient has finite compact-band quadratic energy under canonical C2 domain
-- statement:
--   For the genuine source SpectrallyNegativeLevy X and its original admissible dividend control, a compact pre-jump reserve band lying strictly within the canonical 0<y and ENNReal.ofReal y<C C2 region has a predictable masked gradient with finite L2 energy against every finite source-predictable clock measure. This gives the exact source-specific boundedness and integrability interface for UBV Gaussian and small-jump localisation, at both finite and infinite caps, without asserting an Ito formula or stoppage exhaustion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_allcap_original_predictable_gradient_compact_L2_from_C2_domain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by sorry
