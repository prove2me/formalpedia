-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_shifted_pre_ruin_regulated_band
-- name    : AvramDividend.Classical.avram_chat24_original_shifted_pre_ruin_regulated_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:41:08.697053+00:00
-- url     : https://prove2.me/theorems/90a8b2df-9e5e-45e4-8b34-37ddb126af5d
-- title:
--   Original shifted pre-ruin reserve band and predictable left convergence
-- statement:
--   Source-faithful child of 33a32b0b-5c11-425c-8625-13559c4d089c. Prove the actual original shifted reserve bounds and its predictable left limit before original ruin. No convergence of grids, occupation certificate, or stochastic budget is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_shifted_pre_ruin_regulated_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let b : ℝ := x + δ + T * X.drift
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + δ + X.X s p.2 - rightLimit D s p.2) p.1
    ∀ᵐ ω ∂P, ∀ B : ℝ≥0, B ≤ S → (B : ℝ≥0∞) < ruinTime X x D ω →
      (∀ s : ℝ≥0, s ≤ B → riskProcess X x D s ω + δ ∈ Icc δ b) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ B →
        Y (t, ω) ∈ Icc δ b ∧
        Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω + δ)
          (𝓝[<] t) (nhds (Y (t, ω))) := by sorry
