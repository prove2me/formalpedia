-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_compact_generator_physical_fibre_L1
-- name    : AvramDividend.Classical.avram_ubv_top9_source_topcap_compact_generator_physical_fibre_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:53:43.52363+00:00
-- url     : https://prove2.me/theorems/356878b6-458d-4565-98ef-b08748f7a343
-- title:
--   The original infinite-cap compact HJB drift has integrable physical time fibres
-- statement:
--   For the same original spectrally negative Levy reserve, genuine pre-right-payment risk, actual ruin mask and finite time horizon, the compact positive-interior generator-minus-discount drift has an integrable physical time integral. The source predictable HJB measure agrees with the physical time-law product; the original Levy process supplies its probability-measure instance. This resolves the required L1 Fubini transfer without assuming an auxiliary or finite-cap process.
-- source:
--   Proved ca1e7b57 topcap original predictable Gaussian gradient and HJB drift source; Proved avram_p3_b_bvjump_original_predictable_le_product_space and independently accepted proof e7333410 demonstrating measure trim and Integrable.integral_prod_right. Intended for 25573e81 and conditional jump-HJB sign theorem 0560d7c6; does not itself prove Ito.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_source_topcap_compact_generator_physical_fibre_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D) (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b) (hb : b < B)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    Integrable (fun ω : Ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂
        (((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
