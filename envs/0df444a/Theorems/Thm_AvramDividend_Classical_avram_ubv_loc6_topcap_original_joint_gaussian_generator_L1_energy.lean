-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_joint_gaussian_generator_L1_energy
-- name    : AvramDividend.Classical.avram_ubv_loc6_topcap_original_joint_gaussian_generator_L1_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:26:02.362508+00:00
-- url     : https://prove2.me/theorems/2420fd8e-df39-4d01-bc92-0f8e3ec12292
-- title:
--   Original infinite-cap same predictable-clock HJB drift and Gaussian square energy
-- statement:
--   For every finite real interior strip under original infinite cap, the exact physical predictable-clock measure simultaneously supports the integrable nonpositive generator drift and finite square energy of the clipped discounted Gaussian coefficient. Both use the same original reserve/right-limit dividend process.
-- source:
--   Compose the source-exact topcap original compact generator HJB L1 theorem with Proved original physical Gaussian finite joint energy 4382bab8 at the identical finite predictable measure; boundary exhaustion remains open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_topcap_original_joint_gaussian_generator_L1_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hTop : C = ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ B : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < B)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ v then y else δ
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ := by sorry
